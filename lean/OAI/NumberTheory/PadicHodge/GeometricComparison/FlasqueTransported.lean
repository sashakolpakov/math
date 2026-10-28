import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTransportedGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.InverseCech

/-! # Flasque Transported -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueTransported.FlasqueTransportedEdgeCoordinates

noncomputable section

/-! The transported global edge is determined degree by degree by
its original inverse comparison on the zero Cech column. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v w s t
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)) ℕ)
  {C : Type s} [Category.{t} C] [HasBinaryProducts C] (F : C ⥤ Opens X)
  {ι : Type} (U : ι → C)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  {Q : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{max u v w} R) ℕ}
  {N : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v w} R) ℕ}
  (e₀ : N ≅ ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{max u v w} R) F).mapHomologicalComplex (.up ℕ)).obj Q)
  (e₁ : FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K ≅ Q)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex R X K

theorem inverse_edge : FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.edge R X K F U e₀ e₁ =
    FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K ≫
      (FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.comparisonIso R X K F U e₀ e₁).inv := by
  let a := FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.edge R X K F U e₀ e₁
  let e := FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.comparisonIso R X K F U e₀ e₁
  exact (Category.comp_id a).symm.trans
    ((congrArg (fun x => a ≫ x) e.hom_inv_id.symm).trans
      ((Category.assoc a e.hom e.inv).symm.trans
        (congrArg (fun x => x ≫ e.inv) (FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.comparison R X K F U e₀ e₁))))

theorem inverse_component (q : ℕ) : (FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.edge R X K F U e₀ e₁).f q =
    FlasqueCechGlobal.FlasqueCechGlobalComparison.component R X (F.obj ∘ U) K q ≫
      ((Cech.TransportedCone.CechTransportedCone.bicomplexIso F U e₀ e₁).inv.f q).f 0 ≫
        (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U N).ιTotal (.up ℕ) q 0 q rfl :=
  (congrArg (fun a => a.f q) (inverse_edge R X K F U e₀ e₁)).trans
    (InverseCech.InverseCechEdgeCoordinates.component (FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K)
      (Cech.TransportedCone.CechTransportedCone.bicomplexIso F U e₀ e₁).inv q
      (FlasqueCechGlobal.FlasqueCechGlobalComparison.component R X (F.obj ∘ U) K q) rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueTransported.FlasqueTransportedEdgeCoordinates
