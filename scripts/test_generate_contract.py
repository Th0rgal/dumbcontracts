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

from generate_contract import (
    ContractConfig,
    Field,
    Function,
    Param,
    gen_all_lean_imports,
    gen_basic_proofs,
    gen_property_tests,
    parse_fields,
    parse_functions,
    scaffold_files,
)


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


class GenerateContractFunctionSignatureValidationTests(unittest.TestCase):
    def _assert_parse_functions_error(self, spec: str) -> str:
        buf = io.StringIO()
        with redirect_stderr(buf):
            with self.assertRaises(SystemExit) as ctx:
                parse_functions(spec, [])
        self.assertEqual(ctx.exception.code, 1)
        return buf.getvalue()

    def test_rejects_unbalanced_parentheses_in_function_list(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256)),bar(")
        self.assertIn("Malformed function list", err)
        self.assertIn("unexpected ')'", err)

    def test_rejects_unknown_parameter_type(self) -> None:
        err = self._assert_parse_functions_error("foo(bytes32)")
        self.assertIn("Unsupported parameter type 'bytes32'", err)

    def test_rejects_extra_closing_parenthesis(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256))")
        self.assertIn("unexpected ')'", err)

    def test_rejects_empty_signature_entry(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256),,bar(address)")
        self.assertIn("empty signature between commas", err)

    def test_rejects_trailing_comma(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256),")
        self.assertIn("empty signature at end of list", err)

    def test_parses_valid_typed_signatures(self) -> None:
        funcs = parse_functions("transfer(address,uint256),getBalance(address)", [])
        self.assertEqual([f.name for f in funcs], ["transfer", "getBalance"])
        self.assertEqual([p.ty for p in funcs[0].params], ["address", "uint256"])
        self.assertEqual([p.ty for p in funcs[1].params], ["address"])


class GenerateContractGetterPropertyScaffoldTests(unittest.TestCase):
    def test_getter_scaffold_is_explicit_todo_placeholder(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[Function(name="getStoredValue", params=[])],
        )

        out = gen_property_tests(cfg)
        self.assertIn(
            "function testTODO_GetStoredValue_GetterNeedsSpecAssertions() public {",
            out,
        )
        self.assertIn("Property TODO: getStoredValue_meets_spec", out)
        self.assertIn("revert(\"TODO: implement getter property assertions\");", out)
        self.assertNotIn("bytes memory data", out)
        self.assertNotIn("assertEq(readStorage(0), slot0Before", out)

    def test_non_getter_scaffold_keeps_meets_spec_template(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[
                Function(
                    name="setStoredValue",
                    params=[Param(name="value", ty="uint256")],
                )
            ],
        )

        out = gen_property_tests(cfg)
        self.assertIn("function testProperty_SetStoredValue_MeetsSpec() public {", out)
        self.assertIn("Property: setStoredValue_meets_spec", out)


class GenerateContractBasicProofScaffoldTests(unittest.TestCase):
    def test_basic_proof_scaffold_has_no_sorry(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[
                Function(name="getStoredValue", params=[]),
                Function(
                    name="setStoredValue",
                    params=[Param(name="value", ty="uint256")],
                ),
            ],
        )

        out = gen_basic_proofs(cfg)
        self.assertNotIn("sorry", out)
        self.assertIn("simp [getStoredValue_spec]", out)
        self.assertIn("simp [setStoredValue_spec]", out)


class GenerateContractStructureScaffoldTests(unittest.TestCase):
    def test_scaffold_files_include_ast_and_spec_correctness(self) -> None:
        cfg = ContractConfig(
            name="AuditProbe",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[
                Function(
                    name="setStoredValue",
                    params=[Param(name="value", ty="uint256")],
                )
            ],
        )
        paths = {str(path) for path, _ in scaffold_files(cfg)}

        self.assertIn(str((SCRIPT_DIR.parent / "Verity" / "AST" / "AuditProbe.lean")), paths)
        self.assertIn(
            str((SCRIPT_DIR.parent / "Compiler" / "Proofs" / "SpecCorrectness" / "AuditProbe.lean")),
            paths,
        )

    def test_all_lean_imports_include_ast_module(self) -> None:
        cfg = ContractConfig(
            name="AuditProbe",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[Function(name="getStoredValue", params=[])],
        )
        imports = gen_all_lean_imports(cfg)
        self.assertIn("import Verity.AST.AuditProbe", imports)


if __name__ == "__main__":
    unittest.main()
