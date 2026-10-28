import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Finite Affine -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.FiniteAffine.BundleCycles

noncomputable section

/-! # LineBundleCycles: every finite family of points in a projective complex scheme has a common affine neighborhood -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

def projectiveVanishingLinearForms (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :=
  (x.asHomogeneousIdeal.toIdeal.restrictScalars ℂ).comap (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1).subtype

theorem projectiveVanishingLinearForms_ne_top (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    projectiveVanishingLinearForms n x ≠ ⊤ := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n x
  have hn := (Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen n i x).mp hi
  intro he
  have hm : (⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩ : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) ∈
      projectiveVanishingLinearForms n x := by rw [he]; exact Submodule.mem_top
  exact hn hm

theorem exists_projective_linearForm_avoiding {ι : Type*} [Finite ι]
    (n : ℕ) (x : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1, ∀ i, a.val ∉ (x i).asHomogeneousIdeal :=
  Submodule.exists_forall_notMem_of_forall_ne_top (fun i => projectiveVanishingLinearForms n (x i))
    (fun i => projectiveVanishingLinearForms_ne_top n (x i))

theorem exists_projectiveSpace_commonAffine {ι : Type*} [Finite ι]
    (n : ℕ) (x : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    ∃ U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨a, ha⟩ := exists_projective_linearForm_avoiding n x
  exact ⟨Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) a.val,
    Proj.isAffineOpen_basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) a.val a.property Nat.zero_lt_one,
    fun i => (Proj.mem_basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) a.val (x i)).mpr (ha i)⟩

theorem exists_projective_commonAffine {X : Scheme.{0}} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) {ι : Type*} [Finite ι] (x : ι → X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨U, hU, hx⟩ := exists_projectiveSpace_commonAffine P.ambientDimension (fun i => P.embedding (x i))
  exact ⟨P.embedding ⁻¹ᵁ U, hU.preimage P.embedding, hx⟩

theorem exists_affineOverProjective_commonAffine {X Y : Scheme.{0}} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) (q : Y ⟶ X) [IsAffineHom q]
    {ι : Type*} [Finite ι] (x : ι → Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨U, hU, hx⟩ := exists_projective_commonAffine P (fun i => q (x i))
  exact ⟨q ⁻¹ᵁ U, hU.preimage q, hx⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.FiniteAffine.BundleCycles
