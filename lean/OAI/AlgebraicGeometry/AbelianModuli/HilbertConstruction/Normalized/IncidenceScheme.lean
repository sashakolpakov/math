import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.Incidence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus

/-! # Incidence Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.IncidenceScheme

noncomputable section

/-!
Kernel-preserving linear maps form actual closed incidence loci on normalized
Grassmannian charts. The representation applies to every test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus

universe u

variable {ι ν κ μ : Type u} [Fintype ι] [Fintype ν] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq μ]

def normalizedIncidenceCondition {R T : Type u} [CommRing R] [CommRing T]
    (Q : Matrix ι ν R) (K : Matrix κ μ R) (F : Matrix μ ν R) (φ : R →+* T) : Prop :=
  (Matrix.toLin' (Q.map φ)).ker ≤
    ((Matrix.toLin' (K.map φ)).ker).comap (Matrix.toLin' (F.map φ))

theorem normalizedIncidenceCondition_iff {R T : Type u} [CommRing R] [CommRing T]
    (a : ι → ν) (Q : Matrix ι ν R) (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q)
    (K : Matrix κ μ R) (F : Matrix μ ν R) (φ : R →+* T) :
    normalizedIncidenceCondition Q K F φ ↔
      ∀ p : κ × ν, φ (Incidence.normalizedIncidenceMatrix a Q K F p.1 p.2) = 0 := by
  rw [normalizedIncidenceCondition,
    ← Incidence.normalizedIncidenceMatrix_eq_zero_iff a _ (hQ.map φ), ← Incidence.normalizedIncidenceMatrix_map]
  constructor
  · intro h p
    exact congrArg (fun M : Matrix κ ν T => M p.1 p.2) h
  · intro h
    ext i j
    exact h (i, j)

variable {S : Scheme.{u}} (M : Over S) (a : ι → ν)
variable (Q : Matrix ι ν Γ(M.left, ⊤)) (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q)
variable (K : Matrix κ μ Γ(M.left, ⊤)) (F : Matrix μ ν Γ(M.left, ⊤))

def normalizedIncidenceSubfunctor : Subfunctor (yoneda.obj M) where
  obj T := {x | normalizedIncidenceCondition Q K F x.left.appTop.hom}
  map f x hx := by
    apply (normalizedIncidenceCondition_iff a Q hQ K F _).mpr
    intro p
    change f.unop.left.appTop (x.left.appTop (Incidence.normalizedIncidenceMatrix a Q K F p.1 p.2)) = 0
    rw [(normalizedIncidenceCondition_iff a Q hQ K F _).mp hx p, map_zero]

/-- Actual scheme-theoretic incidence, including nilpotent test schemes. -/
theorem normalized_incidence_representable :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∃ e : yoneda.obj Z ≅ (normalizedIncidenceSubfunctor M a Q hQ K F).toFunctor,
        e.hom ≫ (normalizedIncidenceSubfunctor M a Q hQ K F).ι = yoneda.map j := by
  let s (p : κ × ν) : Γ(M.left, ⊤) := Incidence.normalizedIncidenceMatrix a Q K F p.1 p.2
  have he : normalizedIncidenceSubfunctor M a Q hQ K F = HilbertScheme.Presentations.SectionZeroLocus.sectionZeroSubfunctor M s := by
    ext T x
    exact normalizedIncidenceCondition_iff a Q hQ K F x.left.appTop.hom
  rw [he]
  exact HilbertScheme.Presentations.SectionZeroLocus.section_zero_locus_representable M s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.IncidenceScheme
