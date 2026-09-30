# Project 1: natural numbers in Lean

This is a small Lean 4 project with **no Mathlib dependency**. The repository pins
the Lean compiler version in `lean-toolchain` and uses Lake only to build the
student file.

## Open in GitHub Codespaces

1. Open this repository on GitHub and choose **Code → Codespaces → Create codespace on main**.
2. Wait for the dev container to finish building, then open `NaturalNumbers.lean`.
   The Lean 4 extension is installed automatically; its Infoview shows goals and
   errors as you work.
3. To check the whole project, run `lake build` in the Codespaces terminal.

The container installs Elan and the pinned Lean release. It does not download
Mathlib or run `lake exe cache get`. The first Codespace creation still needs to
download the base container image, the Lean toolchain, and the VS Code extension.
Later builds may reuse cached layers. If Codespaces prebuilds are enabled for
this repository, the class can share an already-built development image.

## Working locally

Install [Elan](https://lean-lang.org/install/manual/) and the
[Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4),
then open the repository and run `lake build`. Elan reads `lean-toolchain` and
installs the pinned compiler on first use.

## Starting the mathematics

Work in `NaturalNumbers.lean`. Define an inductive type of your own inside the
`Project1` namespace, then define operations and prove their properties. Lean's
core library already has a built-in `Nat` type; the goal here is to develop
your own type and results without relying on its arithmetic or on Mathlib.
