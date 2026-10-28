import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeIsomorphismAdditiveSheaves

/-! # Scheme Isomorphism Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeIsomorphismCohomology.ZariskiCohomology

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

/-- Cohomology subsingletonness transports back across a scheme isomorphism. -/
theorem sheafH_subsingleton_of_iso
    {X Y : Scheme.{u}} (e : X ≅ Y) (F : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj F) n)] :
    Subsingleton (CategoryTheory.Sheaf.H F n) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base
  let E := SchemeIsomorphismAdditiveSheaves.ZariskiCohomology.sheafEquivOfSchemeIso e
  let : P.IsEquivalence := by
    change E.functor.IsEquivalence
    infer_instance
  let : PreservesFiniteLimits P := by infer_instance
  let : PreservesFiniteColimits P := by infer_instance
  let : P.PreservesZeroMorphisms := by infer_instance
  let : P.Additive := P.additive_of_preserves_binary_products
  let : P.PreservesInjectiveObjects := by infer_instance
  let hH : Subsingleton (CategoryTheory.Sheaf.H (P.obj F) n) := by
    dsimp [P]
    infer_instance
  let Z := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))
  let κ := SchemeIsomorphismAdditiveSheaves.ZariskiCohomology.pushforwardConstantIso e
  have htarget : Subsingleton (Abelian.Ext (P.obj Z) (P.obj F) n) := by
    refine ⟨fun a b ↦ ?_⟩
    have h := @Subsingleton.elim
      (CategoryTheory.Sheaf.H (P.obj F) n) hH
      ((Abelian.Ext.mk₀ κ.inv).comp a (zero_add n))
      ((Abelian.Ext.mk₀ κ.inv).comp b (zero_add n))
    calc
      a = (Abelian.Ext.mk₀ (𝟙 (P.obj Z))).comp a (zero_add n) :=
        (Abelian.Ext.mk₀_id_comp a).symm
      _ = (Abelian.Ext.mk₀ (κ.hom ≫ κ.inv)).comp a
          (zero_add n) := by rw [κ.hom_inv_id]
      _ = (Abelian.Ext.mk₀ κ.hom).comp
          ((Abelian.Ext.mk₀ κ.inv).comp a (zero_add n))
            (zero_add n) :=
        (Abelian.Ext.mk₀_comp_mk₀_assoc κ.hom κ.inv a).symm
      _ = (Abelian.Ext.mk₀ κ.hom).comp
          ((Abelian.Ext.mk₀ κ.inv).comp b (zero_add n))
            (zero_add n) := congrArg
        (fun z ↦ (Abelian.Ext.mk₀ κ.hom).comp z (zero_add n)) h
      _ = (Abelian.Ext.mk₀ (κ.hom ≫ κ.inv)).comp b
          (zero_add n) :=
        Abelian.Ext.mk₀_comp_mk₀_assoc κ.hom κ.inv b
      _ = (Abelian.Ext.mk₀ (𝟙 (P.obj Z))).comp b (zero_add n) := by
        rw [κ.hom_inv_id]
      _ = b := Abelian.Ext.mk₀_id_comp b
  refine ⟨fun a b ↦ ?_⟩
  apply (P.mapExt_bijective_of_preservesInjectiveObjects Z F n).injective
  exact @Subsingleton.elim _ htarget _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeIsomorphismCohomology.ZariskiCohomology
