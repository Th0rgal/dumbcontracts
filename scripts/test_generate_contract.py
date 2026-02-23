#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from generate_contract import parse_fields, parse_functions


class GenerateContractIdentifierValidationTests(unittest.TestCase):
    def _assert_exits_with_error(self, fn, *args: object) -> str:
        buf = io.StringIO()
        with redirect_stderr(buf):
            with self.assertRaises(SystemExit) as ctx:
                fn(*args)
        self.assertEqual(ctx.exception.code, 1)
        return buf.getvalue()

    def test_parse_fields_rejects_hyphenated_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "bad-name:uint256")
        self.assertIn("Invalid field identifier 'bad-name'", err)

    def test_parse_fields_rejects_leading_digit_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "1field:uint256")
        self.assertIn("Invalid field identifier '1field'", err)

    def test_parse_fields_rejects_reserved_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "contract:uint256")
        self.assertIn("Invalid field identifier 'contract'", err)
        self.assertIn("reserved", err)

    def test_parse_functions_rejects_hyphenated_identifier(self) -> None:
        err = self._assert_exits_with_error(
            parse_functions,
            "set-value(uint256),getValue()",
            [],
        )
        self.assertIn("Invalid function identifier 'set-value'", err)

    def test_parse_functions_rejects_leading_digit_identifier(self) -> None:
        err = self._assert_exits_with_error(
            parse_functions,
            "1setter(uint256)",
            [],
        )
        self.assertIn("Invalid function identifier '1setter'", err)

    def test_parse_functions_rejects_reserved_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_functions, "return(uint256)", [])
        self.assertIn("Invalid function identifier 'return'", err)
        self.assertIn("reserved", err)

    def test_parse_fields_and_functions_accept_valid_identifiers(self) -> None:
        fields = parse_fields("storedData:uint256,owner_address:address")
        funcs = parse_functions("setStoredData(uint256),getStoredData()", fields)
        self.assertEqual([f.name for f in fields], ["storedData", "owner_address"])
        self.assertEqual([f.name for f in funcs], ["setStoredData", "getStoredData"])


if __name__ == "__main__":
    unittest.main()
