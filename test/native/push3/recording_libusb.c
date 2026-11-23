/* Link-free replay of the public libusb calls used by the tethered display.
 * Descriptor fields reflect the published hardware observation. Only the display
 * and xPort interfaces are reconstructed here; this is not a captured USB dump. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

static int stage, push2, push3;
static void *list[] = { &push2, &push3, NULL };
static int counters[8], failure;
enum { INIT, EXIT, OPEN, CLOSE, CLAIM, RELEASE, HEADER, FRAME };
void replay_reset(int mode) { memset(counters, 0, sizeof counters); failure = mode; }
int replay_count(int i) { return counters[i]; }
int libusb_init(void **ctx) { *ctx = &stage; ++counters[INIT]; return 0; }
void libusb_exit(void *ctx) { ++counters[EXIT]; }
ptrdiff_t libusb_get_device_list(void *ctx, void ***out) { *out = list; return 2; }
void libusb_free_device_list(void **devices, int unref) {}
int libusb_get_device_descriptor(void *d, void *out) {
    uint16_t ids[] = {0x2982, d == &push3 ? 0x1969 : 0x1967};
    memset(out, 0, 18);
    memcpy((uint8_t *)out + 8, ids, sizeof ids);
    ((uint8_t *)out)[17] = 1;
    return 0;
}
uint8_t libusb_get_bus_number(void *d) { return 2; }
uint8_t libusb_get_device_address(void *d) { return d == &push3 ? 7 : 5; }
int libusb_open(void *d, void **handle) {
    if (d != &push3) return -4;
    *handle = d; ++counters[OPEN]; return 0;
}
void libusb_close(void *d) { ++counters[CLOSE]; }
int libusb_get_configuration(void *d, int *out) { *out = failure == 1 ? 2 : 1; return 0; }
int libusb_control_transfer(void *d, uint8_t type, uint8_t request, uint16_t value,
                            uint16_t index, uint8_t *data, uint16_t len, unsigned timeout) {
    uint8_t config[] = {
        9,2,48,0,2,1,0,128,50,
        9,4,0,0,2,255,255,255,4, 7,5,1,2,0,2,0, 7,5,129,2,0,2,0,
        9,4,6,0,1,255,255,255,5, 7,5,4,2,0,2,0
    };
    if (type != 128 || request != 6 || value != 512 || index || (len != 9 && len != sizeof config)) return -2;
    if (failure == 2) config[20] = 4;
    memcpy(data, config, len);
    return len;
}
int libusb_get_string_descriptor_ascii(void *d, uint8_t idx, unsigned char *out, int n) {
    const char *s = failure == 3 ? "Ableton Push 3 xPort" : "Ableton Push 3 Display";
    if (idx != 4 || strlen(s) > (size_t)n) return -2;
    memcpy(out, s, strlen(s)); return (int)strlen(s);
}
int libusb_claim_interface(void *d, int i) {
    if (i != 0 || failure == 4) return -6;
    ++counters[CLAIM]; return 0;
}
int libusb_release_interface(void *d, int i) {
    if (i) return -2;
    ++counters[RELEASE]; return 0;
}
int libusb_bulk_transfer(void *d, unsigned char ep, unsigned char *data, int n, int *out, unsigned timeout) {
    static const uint8_t header[16] = {255,204,170,136};
    if (ep != 1 || !timeout) return -2;
    if (n == 16 && !memcmp(data,header,n)) ++counters[HEADER];
    else if (n == 327680) ++counters[FRAME];
    else return -2;
    *out = failure == 5 && n == 327680 ? n-1 : n;
    return 0;
}
