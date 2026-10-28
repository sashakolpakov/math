import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleGlobalSectionsIsomorphism

/-! # Section Adjunction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionAdjunction.AffineSectionAdjunction

noncomputable section

/-! The global-sections adjunction over the actual ring of functions of a scheme. -/
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

def sections (X : Scheme.{u}) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.evaluation _ (op ⊤)

def pushforwardIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.Modules.pushforward f ⋙ sections X ≅
      sections Y ⋙ ModuleCat.restrictScalars f.appTop.hom :=
  NatIso.ofComponents (fun M => ModuleCat.isoMk (Iso.refl _) (by
    intro r
    ext x
    rfl)) (by
      intro M N a
      ext x
      rfl)

def affinizationSectionsIso (X : Scheme.{u}) :
    Scheme.Modules.pushforward X.toSpecΓ ⋙ moduleSpecΓFunctor (R := Γ(X, ⊤)) ≅ sections X :=
  NatIso.ofComponents (fun M => ModuleCat.isoMk (Iso.refl _) (by
    intro r
    ext x
    let x' : Γ(M, ⊤) := x
    change r • x' = X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) • x'
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply])) (by
      intro M N a
      ext x
      rfl)

def left (X : Scheme.{u}) : ModuleCat.{u} Γ(X, ⊤) ⥤ X.Modules :=
  tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.toSpecΓ

def adjunction (X : Scheme.{u}) : left X ⊣ sections X :=
  ((tilde.adjunction (R := Γ(X, ⊤))).comp
    (Scheme.Modules.pullbackPushforwardAdjunction X.toSpecΓ)).ofNatIsoRight
      (affinizationSectionsIso X)

theorem pullback_equivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X)

instance left_full (X : Scheme.{u}) [IsAffine X] : (left X).Full := by
  have : (Scheme.Modules.pullback X.toSpecΓ).IsEquivalence := pullback_equivalence (asIso X.toSpecΓ)
  exact inferInstanceAs ((tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.toSpecΓ).Full)

instance left_faithful (X : Scheme.{u}) [IsAffine X] : (left X).Faithful := by
  have : (Scheme.Modules.pullback X.toSpecΓ).IsEquivalence := pullback_equivalence (asIso X.toSpecΓ)
  exact inferInstanceAs ((tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.toSpecΓ).Faithful)

theorem left_quasicoherent (X : Scheme.{u}) [IsAffine X] (A : ModuleCat.{u} Γ(X, ⊤)) :
    ((left X).obj A).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback X.toSpecΓ).app (tilde A)) inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionAdjunction.AffineSectionAdjunction
