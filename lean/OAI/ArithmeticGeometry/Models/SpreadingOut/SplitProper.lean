import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricProper
import OAI.ArithmeticGeometry.Models.SpreadingOut.CommonGeometric
import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenPartitionIso

/-! # Split Proper -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitProper.Construction

noncomputable section

/-! A smooth proper scheme with split geometric components has a smooth
proper coefficient model whose relative components remain split. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.NumberField

universe u

theorem split_smooth_proper_has_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom]
    (hX : Base.Construction.HasSplitGeometricComponents X) :
    ∃ N : Foundations.Constructions.CoefficientModel K X,
      Smooth N.model.hom ∧ IsProper N.model.hom ∧ Base.Construction.HasSplitGeometricComponents N.model := by
  classical
  obtain ⟨n, C, hdis, hcover, hconn⟩ := hX
  let ι := ULift.{u} (Fin n)
  let D : ι → X.left.Opens := fun i ↦ C i.down
  have hDdis : ∀ i j, i ≠ j → Disjoint (D i) (D j) := by
    intro i j hij
    exact hdis i.down j.down (fun h ↦ hij (ULift.ext i j h))
  have hDcover : (⨆ i, D i) = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ ⨆ i, C i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  let Y (i : ι) := OpenOver.Construction.overOpen X (D i)
  have hY (i : ι) : ∃ M : Foundations.Constructions.CoefficientModel K (Y i),
      Smooth M.model.hom ∧ IsProper M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
    have : IsClosedImmersion (D i).ι := SplitCoproducts.Construction.open_partition_closedImmersion D hDdis hDcover i
    have : Smooth (Y i).hom := inferInstanceAs (Smooth ((D i).ι ≫ X.hom))
    have : IsProper (Y i).hom := inferInstanceAs (IsProper ((D i).ι ≫ X.hom))
    have : GeometricallyConnected (Y i).hom := hconn i.down
    have : GeometricallyIrreducible (Y i).hom :=
      SmoothGeometricIntegrality.Construction.smooth_proper_geometricallyConnected_is_geometricallyIrreducible (Y i).hom
    exact GeometricProper.Construction.smooth_proper_geometricallyIrreducible_has_coefficient_model (Y i)
  choose M hM using hY
  obtain ⟨s, P, eP, hP⟩ := CommonGeometric.Construction.finite_geometric_models_common_base Y M hM
  let Q := ProperCoproducts.Construction.overSigma P
  have hsQ : Smooth Q.hom := by
    let : IsZariskiLocalAtSource (@Smooth.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    change Smooth (Sigma.desc (fun i ↦ (P i).hom))
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{u}) (fun i ↦ (hP i).1)
  have hpQ : IsProper Q.hom := ProperCoproducts.Construction.proper_finite_sigma_desc (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s)
    (fun i ↦ (P i).hom) (fun i ↦ (hP i).2.1)
  have hsplit : Base.Construction.HasSplitGeometricComponents Q := by
    apply SplitCoproducts.Construction.overSigma_hasSplitGeometricComponents P
    intro i
    have : GeometricallyIrreducible (P i).hom := (hP i).2.2
    exact SplitCoproducts.Construction.geometricallyConnected_of_geometricallyIrreducible (P i).hom
  let eQ : (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj Q ≅ X :=
    ProperCoproducts.Construction.overSigmaBaseChangeIso _ P ≪≫ ProperCoproducts.Construction.overSigmaIso eP ≪≫ OpenPartitionIso.Construction.overOpenPartitionIso X D hDdis hDcover
  let N : Foundations.Constructions.CoefficientModel K X := {
    coefficients := s
    model := Q
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := eQ }
  exact ⟨N, hsQ, hpQ, hsplit⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitProper.Construction
