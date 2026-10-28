import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImmersionFiniteCoefficientDescent
import OAI.ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent

/-! # Separated Finite Coefficient Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SeparatedFiniteCoefficientDescent

noncomputable section

/-! Separatedness of a finite-type Noetherian model descends from an
arbitrary coefficient algebra by applying immersion descent to its diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem separated_eventually_of_finiteType
    (C B : Type) [CommRing C] [CommRing B] [Algebra C B] [IsNoetherianRing C]
    (M : Over (Spec (.of C))) [hft : LocallyOfFiniteType M.hom] [hqc : QuasiCompact M.hom]
    [IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C B)))).obj M).hom] :
    ∃ s : Finset B,
      IsSeparated ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s)).obj M).hom := by
  have : IsNoetherian M.left := Finite.TypeParameterNoetherian.finiteType_noetherian_source M.hom
  have hpb := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd M M)
  have : LocallyOfFiniteType (prod.snd : M ⨯ M ⟶ M).left :=
    MorphismProperty.of_isPullback hpb hft
  have : QuasiCompact (prod.snd : M ⨯ M ⟶ M).left :=
    MorphismProperty.of_isPullback hpb hqc
  have : IsNoetherian (M ⨯ M).left := Finite.TypeParameterNoetherian.finiteType_noetherian_source (prod.snd : M ⨯ M ⟶ M).left
  have : QuasiCompact (Limits.diag M).left := inferInstance
  have : IsImmersion (Limits.diag M).left := by
    have : IsImmersion ((Limits.diag M).left ≫ (Over.prodLeftIsoPullback M M).hom) := by
      rw [ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent.Construction.over_diagonal_comp]
      infer_instance
    exact IsImmersion.of_comp (Limits.diag M).left (Over.prodLeftIsoPullback M M).hom
  have : IsClosedImmersion
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C B)))).map (Limits.diag M)).left :=
    (ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent.Construction.baseChange_diagonal_closed_iff _ M).mpr inferInstance
  obtain ⟨s, hs⟩ := ImmersionFiniteCoefficientDescent.closedImmersion_eventually_of_immersion C B (Limits.diag M)
  exact ⟨s, (ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent.Construction.baseChange_diagonal_closed_iff _ M).mp hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SeparatedFiniteCoefficientDescent
