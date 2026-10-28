import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Section Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase

noncomputable section

/-!
# IntegralComparison: canonical affine-open section rings retain their native base structure
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))
  (U : X.left.Opens) (hU : IsAffineOpen U)

theorem overBase : hU.fromSpec ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k ((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)))) := by
  have h := (IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Spec (CommRingCat.of k))) hU
    (show U ≤ X.hom ⁻¹ᵁ ⊤ by simp)).symm
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h

variable (C : Type u) [CommRing C]
  (g : Spec (CommRingCat.of C) ⟶ X.left) [IsOpenImmersion g] (h : U ≤ g.opensRange)

theorem range_subset : U ≤ g.opensRange → Set.range hU.fromSpec ⊆ Set.range g := by
  intro h
  rw [hU.range_fromSpec]
  exact h

def lift : Spec Γ(X.left, U) ⟶ Spec (CommRingCat.of C) :=
  IsOpenImmersion.lift g hU.fromSpec (range_subset k X U hU C g h)

theorem lift_fac : SectionBase.lift k X U hU C g h ≫ g = hU.fromSpec :=
  IsOpenImmersion.lift_fac g hU.fromSpec (range_subset k X U hU C g h)

instance lift_open : IsOpenImmersion (SectionBase.lift k X U hU C g h) := by
  have : IsOpenImmersion (SectionBase.lift k X U hU C g h ≫ g) := (SectionBase.lift_fac k X U hU C g h).symm ▸ inferInstance
  exact IsOpenImmersion.of_comp _ g

def ringMap : CommRingCat.of C ⟶ Γ(X.left, U) := Spec.preimage (SectionBase.lift k X U hU C g h)

theorem ringMap_etale : (ringMap k X U hU C g h).hom.Etale := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
  have he : Spec.map (ringMap k X U hU C g h) = SectionBase.lift k X U hU C g h := Spec.map_preimage _
  rw [he]
  infer_instance

variable [Algebra k C] (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k C)))

include hg in
theorem ringMap_base : CommRingCat.ofHom (algebraMap k C) ≫ ringMap k X U hU C g h =
    CommRingCat.ofHom (algebraMap k ((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U))) := by
  apply Spec.map_injective
  have h₁ : Spec.map (ringMap k X U hU C g h) = SectionBase.lift k X U hU C g h := Spec.map_preimage _
  have h₂ := (congrArg (fun f => SectionBase.lift k X U hU C g h ≫ f) hg.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ X.hom) (SectionBase.lift_fac k X U hU C g h)).trans (overBase k X U hU)))
  exact (Spec.map_comp _ _).trans
    ((congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap k C))) h₁).trans h₂)

def algHom : CommAlgCat.of k C ⟶ (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U) :=
  CommAlgCat.ofHom
    { (ringMap k X U hU C g h).hom with
      commutes' := fun r => ConcreteCategory.congr_hom (ringMap_base k X U hU C g h hg) r }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
