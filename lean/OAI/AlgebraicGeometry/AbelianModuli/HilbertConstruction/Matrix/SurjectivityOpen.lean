import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityMinors
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

/-! # Surjectivity Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityOpen

noncomputable section

/-! Maximal minors define an actual open subset representing affine matrix-surjectivity tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

def matrixSurjectiveOpen {X : Scheme.{u}} (F : Matrix ι ν Γ(X, ⊤)) : X.Opens :=
  ⨆ a : ι → ν, X.basicOpen (F.submatrix id a).det

omit [Fintype ν] [DecidableEq ν] in
theorem matrixSurjectiveOpen_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Matrix ι ν Γ(Y, ⊤)) :
    f ⁻¹ᵁ matrixSurjectiveOpen F = matrixSurjectiveOpen (F.map f.appTop.hom) := by
  rw [matrixSurjectiveOpen, f.preimage_iSup]
  apply congrArg iSup
  funext a
  rw [Scheme.preimage_basicOpen_top]
  exact congrArg X.basicOpen (f.appTop.hom.map_det (F.submatrix id a))

theorem matrixSurjectiveOpen_affine {R : CommRingCat.{u}} (F : Matrix ι ν Γ(Spec R, ⊤)) :
    matrixSurjectiveOpen F = ⊤ ↔
      Function.Surjective (Matrix.toLin' (F.map (Scheme.ΓSpecIso R).hom.hom)) := by
  have hm (p : PrimeSpectrum R) : p ∈ matrixSurjectiveOpen F ↔
      ∃ a : ι → ν, ((F.map (Scheme.ΓSpecIso R).hom.hom).submatrix id a).det ∉ p.asIdeal := by
    have hc : (matrixSurjectiveOpen F : TopologicalSpace.Opens (PrimeSpectrum R)) =
        ⨆ a : ι → ν, PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom (F.submatrix id a).det) := by
      simp only [matrixSurjectiveOpen, basicOpen_eq_of_affine']
      rfl
    refine (Iff.of_eq (congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => p ∈ U) hc)).trans ?_
    refine (TopologicalSpace.Opens.mem_iSup (x := p) (s := fun a : ι → ν =>
      PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom (F.submatrix id a).det))).trans ?_
    simp only [PrimeSpectrum.mem_basicOpen]
    apply exists_congr
    intro a
    rw [(Scheme.ΓSpecIso R).hom.hom.map_det (F.submatrix id a)]
    rfl
  rw [SurjectivityMinors.matrix_surjective_iff_prime_minors]
  constructor
  · intro h p
    apply (hm p).mp
    rw [h]
    trivial
  · intro h
    apply top_unique
    intro p _
    exact (hm p).mpr (h p)

theorem matrixSurjectiveOpen_affine_point {X : Scheme.{u}} {R : CommRingCat.{u}}
    (F : Matrix ι ν Γ(X, ⊤)) (x : Spec R ⟶ X) :
    Set.range x ⊆ (matrixSurjectiveOpen F : Set X) ↔
      Function.Surjective (Matrix.toLin' (F.map (AffineProjective.Charts.affinePointCoefficients x).hom)) := by
  have hr : Set.range x ⊆ (matrixSurjectiveOpen F : Set X) ↔
      x ⁻¹ᵁ matrixSurjectiveOpen F = ⊤ := by
    constructor
    · intro h
      apply top_unique
      intro p _
      exact h ⟨p, rfl⟩
    · intro h z hz
      obtain ⟨p, rfl⟩ := hz
      have hp : p ∈ x ⁻¹ᵁ matrixSurjectiveOpen F := h.symm ▸ (show p ∈ (⊤ : (Spec R).Opens) from trivial)
      exact hp
  rw [hr, matrixSurjectiveOpen_preimage, matrixSurjectiveOpen_affine]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityOpen
