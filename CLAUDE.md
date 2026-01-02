# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean4 formalization of Gödel's ontological argument, rewritten from [iehality/goedelgod](https://github.com/iehality/goedelgod) (Lean3).

## Build Commands

```bash
lake build              # Build the project
lake exe cache get      # Download Mathlib cache (speeds up first build significantly)
```

## Architecture

The project uses Lean 4 with Mathlib as a dependency. Key files:

- **GodExistence/Basic.lean**: Modal logic foundations
  - `Model` structure: Kripke semantics with worlds and accessibility relations
  - Frame conditions: `IsReflexive`, `IsTransitive`, `IsSymmetric`, `IsEuclidean`
  - Modal systems: `IsKTB`, `IsKB4`, `IsS4`, `IsS5`
  - Modal operators: `□` (box/necessity), `◇` (diamond/possibility)
  - Propositional connectives: `∼` (negation), `⋏` (and), `⋎` (or), `➝` (implication), `⭤` (iff)
  - Quantifiers: `∀'`, `∃'` over properties

- **GodExistence/Argument.lean**: Main ontological argument
  - `Godlike`: Definition of God as possessing all positive properties
  - `Essence`: Property necessarily implying all properties of an individual
  - `NecessaryExistence`: Having essence implies necessary existence
  - Key theorems: `necessarily_exists_godlike`, `monotheism`, `modal_collapse`

## Notation Guide

| Symbol | Meaning |
|--------|---------|
| `⊧ φ` | φ is valid (true in all worlds) |
| `□φ` | Necessarily φ |
| `◇φ` | Possibly φ |
| `∀' Φ` | For all properties Φ |
| `∃' Φ` | There exists property Φ |
| `a ≡ₗ b` | Leibniz equality |
