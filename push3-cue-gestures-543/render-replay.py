from __future__ import annotations

import json
import sys
from functools import cache
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


WIDTH, HEIGHT = 1280, 800
BG, INK, MUTED = '#f1f3f7', '#1b2231', '#526179'
WHITE, LINE, ACCENT = '#ffffff', '#dce3ee', '#4e378f'
GREEN, SOFT_GREEN = '#12613d', '#e3f3e9'
ROW_ACTIVE, ROW_PENDING = '#f0ecfb', '#f6f8fc'


@cache
def font(size, weight='regular'):
    if weight == 'mono':
        filename = '/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf'
    else:
        variant = 'Bold' if weight == 'bold' else 'Regular'
        filename = f'/usr/share/fonts/truetype/liberation/LiberationSans-{variant}.ttf'
    return ImageFont.truetype(filename, size)


def label(draw, x, y, value, size=23, color=INK, weight='regular'):
    draw.text((x, y), value, font=font(size, weight), fill=color, anchor='lt')


def pill(draw, x, y, value):
    length = int(draw.textlength(value, font=font(18, 'bold')))
    draw.rounded_rectangle((x, y, x + length + 25, y + 32), 9, fill=SOFT_GREEN)
    label(draw, x + 12, y + 7, value, 18, GREEN, 'bold')


def ms(value):
    return f'{value:,} ms'


def short_op(command):
    return command.get('op', '').rpartition('/')[-1]


def latest_press(events, event):
    _, note, _ = event['midi']
    channel = event['midi'][0] & 15
    return next(before for before in reversed(events[:event['index']])
                if before['profile'] == event['profile'] and before['midi']
                and before['midi'][0] == 0x90 | channel
                and before['midi'][1] == note and before['midi'][2] > 0)


def instance_state(event, id):
    return next((instance['phase'] for instance in event['instances'] if instance['id'] == id), None)


def user_rows(events):
    user = [event for event in events if event['profile'] == 'poly-aftertouch']
    launches = {}
    for event in user:
        for command in event['commands']:
            if short_op(command) == 'launch' and command.get('grid'):
                launches.setdefault(command['command-id'], (command, event))

    rows = []
    for id, (command, admitted) in launches.items():
        states = [(event, receipt) for event in user for receipt in event['receipts']
                  if receipt['command-id'] == id]
        pending, _ = next(pair for pair in states if pair[1]['status'] == 'pending')
        terminal, receipt = next(pair for pair in states if pair[1]['status'] in {'fired', 'cancelled'})
        strike = command['raw']['time-ms']
        strike_event = next(event for event in user if event['time-ms'] == strike and event['midi'])
        held = command['launch']['mode'] == 'held'
        if held:
            note_off = next(event for event in user if event['midi'] and any(
                short_op(cmd) == 'cancel-launch' and cmd['launch-command-id'] == id
                for cmd in event['commands']))
        else:
            note_off = admitted

        cue = command['cue-id'].capitalize()
        press = (strike_event['index'], f"Note {strike_event['midi'][1]}  ↓ {ms(strike)}")
        release_input = (note_off['index'], f"↑ {ms(note_off['time-ms'])}")
        queue = (pending['index'], f"{command['launch']['mode'].capitalize()}  ·  Pending {ms(pending['time-ms'])}")
        if receipt['status'] == 'fired':
            instance = receipt['instance-id']
            result = (terminal['index'], f"Fired {ms(receipt['admitted-at']['time-ms'])}  ·  #{instance}")
            if held:
                released = next(event for event in user if event['index'] > terminal['index']
                                and instance_state(event, instance) == 'releasing')
                later = (released['index'], f"Releasing {ms(released['time-ms'])}  ·  #{instance}")
                heading = ('Hold after grid fire', cue)
            else:
                later = None
                heading = ('Tap', cue)
        else:
            result = (terminal['index'], f"Cancelled {ms(terminal['time-ms'])}")
            later = None
            heading = ('Hold before grid fire', cue)
        rows.append((heading, (press, release_input), (queue,), (result, later)))

    ended, end = next((event, command) for event in user for command in event['commands']
                      if short_op(command) == 'end')
    id = end['instance-id']
    press = latest_press(events, ended)
    cue = next(instance['cue-id'] for instance in ended['instances'] if instance['id'] == id)
    rows.append((('Active tap', cue.capitalize()),
                 ((press['index'], f"Note {press['midi'][1]}  ↓ {ms(press['time-ms'])}"),
                  (ended['index'], f"↑ {ms(ended['time-ms'])}")),
                 ((ended['index'], f'End captured instance #{id}'),),
                 ((ended['index'], f"{instance_state(ended, id).capitalize()} {ms(ended['time-ms'])}  ·  #{id}"),)))
    return rows


def mpe_rows(events):
    def midi_axis(packet):
        return {0xD0: 'Pressure', 0xE0: 'Glide', 0xB0: 'Slide (CC74)'}[packet[0] & 240]

    def value_string(value):
        return '[' + ', '.join(map(str, value)) + ']' if isinstance(value, list) else f'{value:.1f}'

    mpe = [event for event in events if event['profile'] == 'mpe']
    axes = {}
    for event in mpe:
        for command in event['commands']:
            if short_op(command) == 'set' and event['midi']:
                axes.setdefault(command['instance-id'], []).append((event, command))

    rows = []
    for id, edits in axes.items():
        first_edit = edits[0][0]
        channel = first_edit['midi'][0] & 15
        press = next(event for event in mpe if event['midi'] and event['midi'][0] == 0x90 | channel)
        note_off = next(event for event in mpe if event['midi'] and event['midi'][0] == 0x80 | channel)
        actions = [(event['index'], f"{ms(event['time-ms'])}  ·  {midi_axis(event['midi'])}",
                    f"{cmd['param']} = {value_string(cmd['value'])}") for event, cmd in edits]
        rows.append((f"Ch {channel + 1}  ·  Note {press['midi'][1]}", f'#{id}', press['index'], actions,
                     (note_off['index'], f"{instance_state(note_off, id).capitalize()} after note-off · {ms(note_off['time-ms'])}")))
    return rows


def render(capture, user, mpe, user_until, mpe_until, summary, stage):
    image = Image.new('RGB', (WIDTH, HEIGHT), BG)
    draw = ImageDraw.Draw(image)
    label(draw, 54, 31, 'Push 3 cue gestures', 50, weight='bold')
    label(draw, 56, 91, 'Synthetic MIDI replay through the Tolglow show owner', 25, MUTED)
    pill(draw, 1050, 51, 'VIRTUAL MIDI')

    draw.rounded_rectangle((52, 139, 1228, 490), 18, fill=WHITE, outline=LINE, width=2)
    label(draw, 76, 159, 'User Mode', 28, weight='bold')
    label(draw, 240, 164, 'Tap, hold and quantized release', 21, MUTED)
    for x, heading in zip((77, 339, 551, 853), ('Gesture', 'Captured input', 'Profile / queue', 'Show owner')):
        label(draw, x, 204, heading, 17, ACCENT, 'bold')
    for i, (title, pad, queue, owner) in enumerate(user):
        y = 227 + 61 * i
        actual_cells = [cell for column in (pad, queue, owner) for cell in column if cell]
        if mpe_until < 0 and any(cell[0] == user_until for cell in actual_cells):
            draw.rounded_rectangle((65, y, 1215, y + 60), 9, fill=ROW_ACTIVE)
        elif i % 2 == 0:
            draw.rounded_rectangle((65, y, 1215, y + 60), 9, fill=ROW_PENDING)
        if pad[0][0] > user_until:
            continue
        label(draw, 77, y + 10, title[0], 22, weight='bold')
        label(draw, 77, y + 35, title[1], 17, MUTED)
        for x, column in zip((339, 551, 853), (pad, queue, owner)):
            for line_no, cell in enumerate(column):
                if cell and cell[0] <= user_until:
                    color = GREEN if x == 853 and line_no == 0 else INK
                    label(draw, x, y + 11 + 25 * line_no, cell[1], 20, color,
                          'bold' if x == 853 else 'regular')

    draw.rounded_rectangle((52, 507, 1228, 718), 18, fill=WHITE, outline=LINE, width=2)
    label(draw, 76, 528, 'MPE', 28, weight='bold')
    label(draw, 151, 532, 'Two held pads edit their own running instances', 21, MUTED)
    for (voice, id, pressed, actions, release), x in zip(mpe, (76, 649)):
        if pressed > mpe_until:
            continue
        width = 554
        draw.rounded_rectangle((x, 567, x + width, 701), 10, fill=ROW_PENDING)
        label(draw, x + 13, 580, voice, 22, weight='bold')
        label(draw, x + 366, 580, f'Instance {id}', 19, ACCENT, 'bold')
        for i, (index, action, value) in enumerate(actions):
            if index <= mpe_until:
                label(draw, x + 13, 610 + 25 * i, action, 19, MUTED)
                label(draw, x + 267, 609 + 25 * i, value, 20, weight='bold')
        if release[0] <= mpe_until:
            label(draw, x + 13, 668, release[1], 19, GREEN, 'bold')

    draw.line((54, 732, 1226, 732), fill=LINE, width=2)
    label(draw, 55, 745, stage, 19, ACCENT, 'bold')
    label(draw, 205, 745, summary, 19, INK)
    versions = f"Afterglow {capture['afterglow-head'][:8]}  ·  Tolglow {capture['tolglow-head'][:8]}"
    label(draw, 55, 774, versions, 15, MUTED, 'mono')
    return image


def main(source, destination):
    capture = json.loads(source.read_text())
    events = [dict(event, index=index) for index, event in enumerate(capture['events'])]
    user, mpe = user_rows(events), mpe_rows(events)
    assert len(user) == 4 and len(mpe) == 2

    full_user = user[-1][3][-1][0]
    full_mpe = max(row[-1][0] for row in mpe)
    edit_frames = sorted((index, action, value, id[1:]) for _, id, _, actions, _ in mpe
                         for index, action, value in actions)
    summary = f"{capture['results']['pass']} assertions passed · Captured commands, receipts and model state"
    still = render(capture, user, mpe, full_user, full_mpe, summary, 'Replay result')
    still.save(destination.with_suffix('.png'))

    modifier = next(event for event in events[user[2][3][1][0] + 1:user[3][1][0][0]]
                    if event['midi'] and event['midi'][0] & 240 == 0x90
                    and event['selection'] and not event['commands'])
    timeline = [
        ('Pad down', user[0][1][0][0], -1, 'The pad press starts the tap/hold window.'),
        ('Tap', user[0][2][0][0], -1, 'Note-off submits a persistent launch to the grid.'),
        ('First beat', user[0][3][0][0], -1, 'The owner fires the tap and records the instance.'),
        ('Hold deadline', user[1][2][0][0], -1, 'The profile classifies the held pad and queues a launch.'),
        ('Early release', user[1][3][0][0], -1, 'Note-off cancels the pending launch by its ID.'),
        ('Second beat', user[2][3][0][0], -1, 'The second hold fires and records a separate instance.'),
        ('Held release', user[2][3][1][0], -1, 'Note-off releases the instance from the fired hold.'),
        ('Modifier', modifier['index'], -1,
         f"Modifier + pad selected #{modifier['selection']} at {ms(modifier['time-ms'])} with no command queued."),
        ('Active tap', full_user, -1, 'The short tap ends the captured running instance.'),
        ('MPE hold', full_user, max(row[2] for row in mpe), 'Two member channels hold separate voices.'),
        *((action.split('  ·  ')[1], full_user, index, f'Applied {value} to instance #{id}.')
          for index, action, value, id in edit_frames),
        ('MPE release', full_user, full_mpe, 'Both instances stay running after note-off.'),
    ]
    frames = [render(capture, user, mpe, a, b, message, title) for title, a, b, message in timeline]
    frames[0].save(destination.with_suffix('.gif'), save_all=True, append_images=[*frames[1:], still],
                   duration=[900] * len(frames) + [2200], loop=0, disposal=2, optimize=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]), Path(sys.argv[2]))
