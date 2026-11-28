import Mathlib

/-!
# A 3-regular counterexample to the Bilu–Linial signing conjecture

Source: https://arxiv.org/abs/2609.15591 ("A 3-regular counterexample to the Bilu–Linial signing
conjecture", 2026)
Credit: @SudharsanAnimations

The paper constructs a finite connected simple cubic graph `F` such that every signing of its
edges yields a signed adjacency matrix with an eigenvalue outside `[-2√2, 2√2]`. This disproves
the Bilu–Linial signing conjecture for general regular graphs (for `d = 3`, `2√(d - 1) = 2√2`).
We state this theorem.

Conventions:
- A simple graph is a `SimpleGraph V` on a finite vertex type `V`; cubic means every vertex has
  degree `3`; connected is `SimpleGraph.Connected`.
- A signing assigns `+1` or `-1` to every edge. It is given by `σ : V → V → ℝ`, symmetric, with
  `σ u v ∈ {1, -1}` whenever `u` and `v` are adjacent (its other values are irrelevant). The
  signed adjacency matrix has entry `σ u v` at adjacent `u, v` and `0` elsewhere; it is a real
  symmetric matrix, so all its eigenvalues are real.
- "An eigenvalue outside `[-2√2, 2√2]`" is a real eigenvalue `μ` of that matrix (as a linear map
  on `V → ℝ`) with `|μ| > 2√2`.
-/

namespace OMA.S_arxiv_2609_15591

/-- The signed adjacency matrix of `G` for the signing `σ`. -/
noncomputable def signedAdj {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : V → V → ℝ) : Matrix V V ℝ :=
  Matrix.of fun u v => if G.Adj u v then σ u v else 0

/-- `σ` is a signing of the edges of `G`. -/
def IsSigning {V : Type} (G : SimpleGraph V) (σ : V → V → ℝ) : Prop :=
  (∀ u v, σ u v = σ v u) ∧ ∀ u v, G.Adj u v → (σ u v = 1 ∨ σ u v = -1)

/-- There is a finite connected simple cubic graph all of whose signings have a signed
adjacency matrix with an eigenvalue outside `[-2√2, 2√2]`. -/
theorem main : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
    (_ : DecidableRel G.Adj), G.Connected ∧ G.IsRegularOfDegree 3 ∧
    ∀ σ : V → V → ℝ, IsSigning G σ →
      ∃ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (signedAdj G σ)) μ ∧
        2 * Real.sqrt 2 < |μ| := by
  sorry

end OMA.S_arxiv_2609_15591
