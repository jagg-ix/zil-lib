# ZIL Certificate JSON Encoding v1

This document specifies the tool-independent JSON format (`ZIL-CERTIFICATE/1`) for derivation certificates of Datalog programs with stratified negation and attributes.

It corresponds to target `CERT-11` in `docs/certifying-datalog.md`, based on the ordered proof graph representation of Tantow, Gerlach, Mennicke, and Krötzsch, *Verifying Datalog Reasoning with Lean* (ITP 2025, section 4.4).

## 1. Top-Level Structure

A certificate is represented as a JSON object with schema identifier `ZIL-CERTIFICATE/1`:

```json
{
  "format": "ZIL-CERTIFICATE/1",
  "version": "1.0",
  "nodes": [
    ...
  ]
}
```

Top-level fields:
- `format` (string, required): Exactly `"ZIL-CERTIFICATE/1"`.
- `version` (string, required): Exactly `"1.0"`.
- `nodes` (array of Node objects, required): Ordered sequence of derivation nodes from `0` to `N - 1`.

## 2. Derivation Node Structure

Each element of `nodes` represents a single grounded fact and its justification:

```json
{
  "index": 0,
  "fact": {
    "subject": "service:web",
    "relation": "calls",
    "object": "service:checkout",
    "attrs": [
      { "key": "priority", "value": 1 }
    ]
  },
  "rule": null,
  "premises": []
}
```

Node fields:
- `index` (integer, required): 0-indexed position of this node in the array. Must strictly equal the array offset ($0, 1, \dots, N-1$).
- `fact` (Fact object, required): The ternary relation tuple `(subject, relation, object)` with optional attributes.
- `rule` (string or null, required):
  - `null` (or omitted) for an initial database fact.
  - String (the rule name) for a fact derived by a program rule.
- `premises` (array of integers, required):
  - Empty (`[]`) for database facts.
  - Array of node indices `[p1, p2, ...]` corresponding to the positive premises of the rule, in the exact order declared by the rule.

## 3. Fact and Attribute Representation

### 3.1 Fact Object
- `subject` (string, required): Entity node identifier (e.g. `"service:web"`, `"user:10"`). Variable identifiers prefixed with `"?"` (e.g. `"?x"`) represent non-ground terms and are refused.
- `relation` (string, required): Relation symbol name (e.g. `"calls"`, `"depends_on"`).
- `object` (string, required): Entity node identifier or value literal.
- `attrs` (array of Attribute objects, optional): Key-value attribute annotations. Defaults to `[]`.

### 3.2 Attribute Object
```json
{
  "key": "weight",
  "value": 3
}
```
- `key` (string, required): Attribute name.
- `value` (JSON value, required):
  - Integer number: represents an integer attribute.
  - String: represents a text attribute.
  - Boolean (`true` / `false`): represents a boolean attribute.
  - Typed Object:
    - `{"decimal": "12.34"}`: decimal value.
    - `{"node": "name"}`: node term.
    - `{"var": "x"}`: variable term.

## 4. Invariants of an Ordered Proof Graph

The certificate must satisfy the following structural and semantic invariants:

1. **Strict Ordering (Acyclicity):**
   Every premise $p \in \text{premises}$ of node $i$ must satisfy:
   $$0 \le p < i$$
   Forward references ($p > i$) and self-references ($p = i$) are prohibited. This invariant guarantees acyclicity and allows validation in a single linear pass over the node array.
2. **Groundness:**
   Every fact in the certificate must be ground (containing no variables in subject, object, or attribute values).
3. **Database Fact Justification:**
   A node with `rule: null` must have `premises: []` and its fact must be present in the initial database of the model.
4. **Derived Fact Justification:**
   A node with a rule name must specify positive premises in the exact order of the rule's positive antecedents. Instantiating the rule with these premises must produce the fact as the rule head, and all negative premises of the rule must have no match in the certificate fact set.
5. **No Duplicate Facts:**
   Each fact may appear at most once in the certificate array.
6. **Model Closure:**
   The certificate must contain the full database and must be closed under all rules of the program: no valid rule instantiation over the certificate's facts can yield a fact missing from the certificate.

## 5. Fault Catalog

The certificate reader and checker detect and refuse eleven distinct fault kinds by name:

| Fault Kind | Condition |
|---|---|
| `order` | A premise index violates $p < i$ (cycle or forward reference). |
| `unjustified` | A derived fact does not match the head of the rule instantiated by its premises. |
| `no-rule` | The rule name does not exist in the program. |
| `unsupported` | A database node (`rule: null`) is not found in the model database. |
| `unjustified` (negative premise) | A negative premise (`NOT ...`) is violated by a fact present in the certificate. |
| `not-closed` | The certificate misses a derived fact entailed by the program rules. |
| `database-missing` | A database fact from the model is missing from the certificate. |
| `unjustified` (premise order) | Premises are supplied in an order differing from the rule's positive premises. |
| `duplicate` | The same fact appears more than once in the certificate. |
| `not-ground` | A fact contains an unbound variable. |
| `malformed` | A database node specifies non-empty premises. |

## 6. Deterministic Byte Emission

To ensure byte-for-byte reproducibility:
- Object keys are emitted in fixed order: `format`, `version`, `nodes`.
- Inside each node: `index`, `fact`, `rule`, `premises`.
- Inside each fact: `subject`, `relation`, `object`, and `attrs` (sorted by `key`).
- Integer values are formatted without leading zeros.
- Emission uses canonical UTF-8 JSON without extraneous whitespace.
