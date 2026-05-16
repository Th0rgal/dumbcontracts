import { readFileSync } from "fs";
import { dirname, join } from "path";
import { fileURLToPath } from "url";
import { bundledLanguages, createHighlighter } from "shiki";

const here = dirname(fileURLToPath(import.meta.url));
const docsRoot = join(here, "..");
const grammar = JSON.parse(readFileSync(join(docsRoot, "syntaxes/verity.tmLanguage.json"), "utf8"));

const sample = `verity_contract Token where
  storage
    balances : Address -> Uint256 := slot 0

  linked_externals
    external quote(Uint256) -> (Uint256)

  function transfer (to : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let bal ← getMapping balances sender
    let next ← requireSomeUint (safeSub bal amount) "insufficient"
    require (amount > 0) "zero amount"
    setMapping balances sender next
    emitEvent "Transfer" [amount] [sender]
    return true
`;

const highlighter = await createHighlighter({
  themes: ["github-light"],
  langs: [
    ...Object.keys(bundledLanguages).filter((lang) => lang !== "mermaid"),
    {
      ...grammar,
      name: "verity",
      aliases: ["vty"],
    },
  ],
});

const tokens = highlighter.codeToTokens(sample, {
  lang: "verity",
  theme: "github-light",
  includeExplanation: true,
}).tokens.flat();

function scopesFor(content) {
  return tokens.flatMap((token) =>
    token.explanation
      .filter((part) => part.content.trim() === content)
      .flatMap((part) => part.scopes.map((scope) => scope.scopeName))
  );
}

const expectations = [
  ["verity_contract", "keyword.declaration.contract.verity"],
  ["Token", "entity.name.type.contract.verity"],
  ["storage", "keyword.other.section.verity"],
  ["balances", "variable.other.storage.verity"],
  ["Address", "storage.type.verity"],
  ["slot", "keyword.other.slot.verity"],
  ["external", "keyword.declaration.external.verity"],
  ["quote", "entity.name.function.external.verity"],
  ["function", "keyword.declaration.function.verity"],
  ["transfer", "entity.name.function.verity"],
  ["msgSender", "support.function.context.verity"],
  ["getMapping", "support.function.storage.verity"],
  ["requireSomeUint", "support.function.control.verity"],
  ["safeSub", "support.function.arithmetic.verity"],
  ["setMapping", "support.function.storage.verity"],
  ["emitEvent", "support.function.control.verity"],
  ["true", "constant.language.boolean.verity"],
];

const failures = expectations.filter(([content, expectedScope]) => {
  const scopes = scopesFor(content);
  return !scopes.includes(expectedScope);
});

if (failures.length > 0) {
  console.error("Verity highlighting scope check failed:");
  for (const [content, expectedScope] of failures) {
    console.error(`- ${content}: expected ${expectedScope}, got ${scopesFor(content).join(", ") || "no token"}`);
  }
  process.exit(1);
}

console.log(`Verified ${expectations.length} Verity syntax highlighting scopes.`);
