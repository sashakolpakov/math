import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.IntegralNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeLevelComparison

/-! # Lattice Map Level Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.LatticeMapLevelComparison

noncomputable section

/-! An integral lattice homomorphism, including a noninvertible
isogeny map, transports the actual full ordered level through its
map modulo N. The comparison holds on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem modNMap_eq_id_of_principal
    {L : Type*} [AddCommGroup L] (N : ℕ) (q : L →+ L)
    (hq : ∀ x, ∃ y, q x - x = N • y) (x : L ⧸ LatticeDivision.TorusTorsion.multipleSubgroup L N) :
    LatticeDivision.TorusTorsion.modNMap N q x = x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [LatticeDivision.TorusTorsion.modNMap_mk]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨w, hw⟩ := hq v
  exact ⟨w, hw.symm⟩

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g N : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem level_comparison_of_marked_lattice_map [NeZero N]
    (α : A.FullLevel N) (β : B.FullLevel N)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (m : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree →ₗ[ℤ] Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B PB σ s hs hg hdegree)
    (hm : ∀ x, (m x).val = u x.val)
    (hf : Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv) =
      (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap)
    (hlevel : ∀ c, LatticeDivision.TorusTorsion.modNMap N m.toAddMonoidHom
      (Intrinsic.OrderedLatticeLevel.markedOrderedLatticeLevel A PA ρ s hs hg hdegree α c) =
        Intrinsic.OrderedLatticeLevel.markedOrderedLatticeLevel B PB σ s hs hg hdegree β c)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N)) :
    (α.hom.app (.op T) c).val ≫ f = (β.hom.app (.op T) c).val := by
  apply Intrinsic.LatticeLevelComparison.level_comparison_of_native_lattice A B PA PB α β f ?_ T c
  intro a
  let eA := (Intrinsic.MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking A PA ρ s hs hg hdegree).toAddEquiv
  let eB := (Intrinsic.MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking B PB σ s hs hg hdegree).toAddEquiv
  apply (LatticeDivision.TorusTorsion.modNEquiv N eB).injective
  have hn := LatticeDivision.TorusTorsion.modNMap_equiv_naturality N eA eB (Intrinsic.DivisionNaturality.originalLatticeMap A B PA PB f).toAddMonoidHom
    m.toAddMonoidHom
    (fun v => Subtype.ext ((IntegralNaturality.nativeIntegralMarking_natural_of_periods
      A B PA PB ρ σ s hs hg hdegree f u hf v).trans (hm _).symm))
    (Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A PA α a)
  exact hn.trans (hlevel a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.LatticeMapLevelComparison
