#!/usr/bin/env python3

from __future__ import annotations

import tempfile
import textwrap
import unittest
from pathlib import Path

import generate_macro_property_tests as gen


class ParseContractsTests(unittest.TestCase):
    def test_parse_two_contracts(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract Counter where
              storage
                count : Uint256 := slot 0

              function increment () : Unit := do
                pure ()

              function getCount () : Uint256 := do
                return 0

            verity_contract Owned where
              storage
                owner : Address := slot 0

              function getOwner () : Address := do
                return 0
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        self.assertEqual(sorted(parsed.keys()), ["Counter", "Owned"])
        self.assertEqual([f.name for f in parsed["Counter"].functions], ["increment", "getCount"])
        self.assertEqual(parsed["Counter"].functions[1].return_type, "Uint256")

    def test_parse_params(self) -> None:
        out = gen._split_params("to : Address, amount : Uint256")
        self.assertEqual([(p.name, p.lean_type) for p in out], [("to", "Address"), ("amount", "Uint256")])


class RenderTests(unittest.TestCase):
    def test_render_unit_and_non_unit_tests(self) -> None:
        contract = gen.ContractDecl(
            name="Sample",
            source=gen.ROOT / "Verity/Examples/MacroContracts.lean",
            functions=(
                gen.FunctionDecl("touch", (), "Unit"),
                gen.FunctionDecl("read", (gen.ParamDecl("who", "Address"),), "Uint256"),
            ),
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Touch_NoUnexpectedRevert()", rendered)
        self.assertIn("function testTODO_Read_DecodeAndAssert()", rendered)
        self.assertIn('abi.encodeWithSignature("read(address)", alice)', rendered)

    def test_render_array_param_adds_helper(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayConsumer",
            source=gen.ROOT / "Verity/Examples/MacroContracts.lean",
            functions=(
                gen.FunctionDecl(
                    "consume",
                    (gen.ParamDecl("values", "Array Uint256"),),
                    "Unit",
                ),
            ),
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("_singletonUintArray", rendered)
        self.assertIn('abi.encodeWithSignature("consume(uint256[])", _singletonUintArray(1))', rendered)

    def test_render_unknown_type_fails_closed(self) -> None:
        contract = gen.ContractDecl(
            name="UnknownType",
            source=gen.ROOT / "Verity/Examples/MacroContracts.lean",
            functions=(
                gen.FunctionDecl("mystery", (gen.ParamDecl("x", "String"),), "Unit"),
            ),
        )
        with self.assertRaisesRegex(ValueError, "unsupported Lean type"):
            gen.render_contract_test(contract)

    def test_render_non_uint_array_fails_closed(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayAddressConsumer",
            source=gen.ROOT / "Verity/Examples/MacroContracts.lean",
            functions=(
                gen.FunctionDecl("consume", (gen.ParamDecl("values", "Array Address"),), "Unit"),
            ),
        )
        with self.assertRaisesRegex(ValueError, "unsupported Lean array element type"):
            gen.render_contract_test(contract)


class CollectContractsTests(unittest.TestCase):
    def test_duplicate_contract_name_errors(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            a = root / "A.lean"
            b = root / "B.lean"
            a.write_text("verity_contract X where\n  storage\n    a : Uint256 := slot 0\n", encoding="utf-8")
            b.write_text("verity_contract X where\n  storage\n    b : Uint256 := slot 0\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate contract 'X'"):
                gen.collect_contracts([a, b])


if __name__ == "__main__":
    unittest.main()
