import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections

/-! # Isomorphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Isomorphism

noncomputable section

/-! An isomorphism of the genuine affine section modules determines
the unique corresponding isomorphism of quasicoherent module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]
  (M N : (Spec (CommRingCat.of R)).Modules) [M.IsQuasicoherent]

local notation "Γₐ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHom.sections (R := R)

def hom (a : (Γₐ).obj M ⟶ (Γₐ).obj N) : M ⟶ N :=
  (Affine.InternalHom.homEquiv M N).symm a

theorem sections_hom (a : (Γₐ).obj M ⟶ (Γₐ).obj N) :
    (Γₐ).map (Isomorphism.hom M N a) = a :=
  (Affine.InternalHom.homEquiv_apply M N _).symm.trans
    ((Affine.InternalHom.homEquiv M N).apply_symm_apply a)

variable [N.IsQuasicoherent]

def iso (e : (Γₐ).obj M ≅ (Γₐ).obj N) : M ≅ N where
  hom := Isomorphism.hom M N e.hom
  inv := Isomorphism.hom N M e.inv
  hom_inv_id := by
    apply (Affine.InternalHom.homEquiv M M).injective
    calc
      _ = (Γₐ).map (Isomorphism.hom M N e.hom ≫ Isomorphism.hom N M e.inv) :=
        Affine.InternalHom.homEquiv_apply M M _
      _ = (Γₐ).map (Isomorphism.hom M N e.hom) ≫ (Γₐ).map (Isomorphism.hom N M e.inv) :=
        (Γₐ).map_comp _ _
      _ = e.hom ≫ e.inv := congrArg₂ (fun a b => a ≫ b)
        (sections_hom M N e.hom) (sections_hom N M e.inv)
      _ = 𝟙 _ := e.hom_inv_id
      _ = (Γₐ).map (𝟙 M) := ((Γₐ).map_id M).symm
      _ = _ := (Affine.InternalHom.homEquiv_apply M M _).symm
  inv_hom_id := by
    apply (Affine.InternalHom.homEquiv N N).injective
    calc
      _ = (Γₐ).map (Isomorphism.hom N M e.inv ≫ Isomorphism.hom M N e.hom) :=
        Affine.InternalHom.homEquiv_apply N N _
      _ = (Γₐ).map (Isomorphism.hom N M e.inv) ≫ (Γₐ).map (Isomorphism.hom M N e.hom) :=
        (Γₐ).map_comp _ _
      _ = e.inv ≫ e.hom := congrArg₂ (fun a b => a ≫ b)
        (sections_hom N M e.inv) (sections_hom M N e.hom)
      _ = 𝟙 _ := e.inv_hom_id
      _ = (Γₐ).map (𝟙 N) := ((Γₐ).map_id N).symm
      _ = _ := (Affine.InternalHom.homEquiv_apply N N _).symm

theorem sections_iso_hom (e : (Γₐ).obj M ≅ (Γₐ).obj N) :
    (Γₐ).map (iso M N e).hom = e.hom := sections_hom M N e.hom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (P Q : X.Modules) [P.IsQuasicoherent] [Q.IsQuasicoherent]
  (e : (Affine.ModuleExactSections.sections U).obj P ≅
    (Affine.ModuleExactSections.sections U).obj Q)

def chartIso : (AffineOpen.InternalHom.chartFunctor U hU).obj P ≅
    (AffineOpen.InternalHom.chartFunctor U hU).obj Q := by
  letI := AffineOpen.InternalHom.chart_quasicoherent U hU P
  letI := AffineOpen.InternalHom.chart_quasicoherent U hU Q
  exact iso _ _ ((Affine.ChartSections.iso U hU P).symm ≪≫ e ≪≫
    Affine.ChartSections.iso U hU Q)

def openIso : P.restrict U.ι ≅ Q.restrict U.ι := by
  let F := Scheme.Modules.restrictFunctor hU.isoSpec.inv
  letI : F.IsEquivalence := inferInstanceAs
    (Scheme.Modules.restrictFunctor hU.isoSpec.symm.hom).IsEquivalence
  exact (Functor.FullyFaithful.ofFullyFaithful F).preimageIso (chartIso U hU P Q e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Isomorphism
