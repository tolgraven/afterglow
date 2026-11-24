from datetime import datetime, timezone
from io import BytesIO
import json
from pathlib import Path
import runpy
import unittest
from unittest.mock import Mock, patch


report = runpy.run_path(str(Path(__file__).with_name("choose-mac-runner")))["reported_result"]


class MacStatusTest(unittest.TestCase):
    def test_individual_statuses_preserve_author_and_attempt(self):
        sha = "a" * 40
        prefix = "local-mac/native-gpu"
        context = f"{prefix}/42.2"
        statuses = [
            {"context": context, "state": "success"},
            {"context": context, "state": "failure", "creator": {"id": 37}},
            {"context": f"{prefix}/42.1", "state": "success", "creator": {"id": 9143357}},
            {"context": context, "state": "pending", "creator": {"id": 9143357},
             "updated_at": datetime.now(timezone.utc).isoformat()},
        ]
        open_history = Mock(return_value=BytesIO(json.dumps(statuses).encode()))
        with patch.dict(report.__globals__, urlopen=open_history):
            self.assertEqual(report("tolgraven/afterglow", sha, "test-token", context), "pending")
        self.assertTrue(open_history.call_args.args[0].full_url.endswith("/statuses?per_page=100"))
