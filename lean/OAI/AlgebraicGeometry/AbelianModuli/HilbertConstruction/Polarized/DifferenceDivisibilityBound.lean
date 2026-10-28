import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonconstantPullbackSectionGrowth
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceDivisionPowerSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.DifferenceSectionBound

/-! # Difference Divisibility Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonconstant restriction of a polarized automorphism difference cannot be divisible by integers whose squares exceed the fixed section bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable {Y : Scheme.{u}} [IsIntegral Y] (i : Y ⟶ A.abelian.scheme.left)
variable [IsClosedImmersion i] [Flat (i ≫ A.abelian.scheme.hom)]
variable [LocallyOfFinitePresentation (i ≫ A.abelian.scheme.hom)]

theorem Moduli.Isomorphisms.LevelPreservingIso.differenceDivisibility_degree_bound (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (hf : ¬ ∃ a : Spec (.of K) ⟶ A.abelian.scheme.left,
      (i ≫ A.abelian.scheme.hom) ≫ a = i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)
    (n : ℕ) (d : A.abelian.EndRing) (hd : n • d = e.endRingUnit.val - 1) :
    n * n + 1 ≤ Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
      ((E.power.pullback i).tensorPower 4).sheaf) := by
  let p := i ≫ A.abelian.scheme.hom
  let v := i ≫ d.toMul.hom.hom.left
  let m := (A.abelian.multiplication n).left
  have hfactor : v ≫ m = i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left :=
    (Category.assoc _ _ _).trans (congrArg (fun f => i ≫ f)
      (congrArg Over.Hom.left (e.difference_factor_of_nsmul n d hd)))
  have hv : ¬ ∃ a : Spec (.of K) ⟶ A.abelian.scheme.left, p ≫ a = v := by
    rintro ⟨a, ha⟩
    exact hf ⟨a ≫ m, (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ m) ha).trans hfactor)⟩
  obtain ⟨hfinite, hbound⟩ := e.differenceSections_finite_and_bound A E i
  let eqv := e.differenceDivisionPowerSectionsIso A E i n d hd
  have : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj
      ((E.power.pullback v).tensorPower (n * n)).sheaf) := (Module.Finite.equiv_iff eqv).mp hfinite
  have : IsProper p := inferInstanceAs (IsProper (i ≫ A.abelian.scheme.hom))
  exact (NonconstantPullbackSectionGrowth.nonconstantMap_powerSections_dimension_lowerBound p A.abelian.scheme.hom E v hv (n * n)).trans
    (eqv.finrank_eq.symm.le.trans hbound)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
