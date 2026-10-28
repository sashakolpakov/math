import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.GlobalConeQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ResolutionQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafMapQuasiIso

/-! # Global Resolution Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.GlobalResolutionQuasiIso

noncomputable section

/-! The genuine global level cone computes injective sections when its
open Čech augmentation and target section comparison do. Source-cone
normalization and section cancellation are combined before specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z r
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D : Type r} [SemilatticeInf D]
  (F : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max w z} R) [F.Additive]
  (G : Sheaf J (ModuleCat.{w} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max w z} R) [G.Additive]
  (e : Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0 ≅ F)
  (b : F ⋙ Functor.const Dᵒᵖ ⟶ G)
  [HasProducts.{0} (Sheaf J (ModuleCat.{w} R))]
  [HasCoproducts.{0} (Sheaf J (ModuleCat.{w} R))]
  {ι : Type} [Finite ι] (U : ι → D)
  (Q : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{w} R) ℕ)
  (P : Dᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : Q ⋙ (constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ) ⟶ P)

local instance constZero : (Functor.const Dᵒᵖ : ModuleCat.{max w z} R ⥤
    Dᵒᵖ ⥤ ModuleCat.{max w z} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable (ψ : Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ) ⋙
    (Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ) ⟶ P ⋙ G.mapHomologicalComplex (.up ℕ))
  (hψ : ConstantSection.OpenTotal.transformation.{u,v,w,z,r,r} R J F G e.hom b Q P a = ψ)
  (h : QuasiIso (Cech.PresheafGlobalAugmentation.map R U
    (Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ))
    (P ⋙ G.mapHomologicalComplex (.up ℕ)) ψ))
  {K I : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (t : K ≅ GeometricComparison.CechCone.Total.CechConeTotal.total U P) (f : K ⟶ I)
  (hmap : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((G.mapHomologicalComplex (.up ℕ)).map f))))
  (hedge : QuasiIso (Presheaf.ConeQuasiIso.map (A := ModuleCat.{max w z} R) U
    (M := (F.mapHomologicalComplex (.up ℕ)).obj I)
    ((b.mapHomologicalComplex (.up ℕ)).app I)))

include hψ h hmap hedge in
theorem quasiIso :
    QuasiIso (ConstantSection.ComplexMap.map.{u,v,w,z} R J
      (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) I
      (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (constantSheaf J (ModuleCat.{w} R)) U Q P a ≫ t.inv ≫ f)) := ConstantSection.ResolutionQuasiIso.quasiIso.{u,v,w,z,r,r}
  R J F G e b U (GeometricComparison.CechCone.Total.CechConeTotal.total U Q)
  (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (constantSheaf J (ModuleCat.{w} R)) U Q P a) t f
  (ConstantSection.GlobalConeQuasiIso.quasiIso R J F G e.hom b U Q P a ψ hψ h)
  hmap hedge

include hψ h hedge in
omit hmap in
theorem quasiIso_of_evaluation
    (hv : ∀ (j : ℕ) (d : Fin (j+1) → ι), QuasiIso
      ((((CategoryTheory.evaluation Dᵒᵖ (ModuleCat.{max w z} R)).obj
        (Opposite.op (∏ᶜ (U ∘ d)))).mapHomologicalComplex (.up ℕ)).map
          ((G.mapHomologicalComplex (.up ℕ)).map f))) :
    QuasiIso (ConstantSection.ComplexMap.map.{u,v,w,z} R J
      (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) I
      (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (constantSheaf J (ModuleCat.{w} R)) U Q P a ≫ t.inv ≫ f)) :=
  quasiIso R J F G e b U Q P a ψ hψ h t f
    (Cech.ConeDiagramQuasiIso.quasiIso.{r,r,w,z} R U
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((G.mapHomologicalComplex (.up ℕ)).map f)) (fun j d => hv j d))
    hedge

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.GlobalResolutionQuasiIso
