import OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledFiberIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TranslationCocycle

/-! # Corrected Subgroup Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CorrectedSubgroupTransport

noncomputable section

/-! Correcting the actual translation defect gives natural, unital, composable line transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledLineIsomorphisms
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios
open Pseudofunctor.LocallyDiscreteOpToCat

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))
  (v : ∀ T : Over (Spec (.of k)), (T ⟶ H) → Γ(T.left, ⊤)ˣ)

/-- Multiply the normalized translation by the inverse regular splitting unit. -/
def transport {T : Over (Spec (.of k))} (x y : T ⟶ A) (a : T ⟶ H) (hx : (a ≫ i) * x = y) :
    Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y :=
  ScaledLineIsomorphisms.rescale (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x y a hx) (v T a)⁻¹

omit [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] in
theorem unit {T : Over (Spec (.of k))} (x : T ⟶ A)
    (hx : ((1 : T ⟶ H) ≫ i) * x = x) (hv : v T 1 = 1) :
    transport i L t v x x 1 hx = Iso.refl (Line.Fibers.fiber L x) := by
  change ScaledLineIsomorphisms.rescale (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x x 1 hx) (v T 1)⁻¹ = _
  rw [Subgroup.TransportUnit.normalized_transport_unit i L t x hx, hv, inv_one, ScaledLineIsomorphisms.rescale_one]

omit [IsAlgClosed k] [IsCommMonObj H] [IsProper A.hom] [IsIntegral A.left] in
theorem natural {T U : Over (Spec (.of k))} (g : U ⟶ T)
    (x y : T ⟶ A) (a : T ⟶ H) (h : (a ≫ i) * x = y)
    (x' y' : U ⟶ A) (a' : U ⟶ H) (h' : (a' ≫ i) * x' = y')
    (hx : g ≫ x = x') (hy : g ≫ y = y') (ha : g ≫ a = a')
    (hv : Units.map g.left.appTop.hom (v T a) = v U a') :
    pullHom (F := Geometric.KernelLinearization.overModulePullbacks (Spec (.of k))) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := x) (f₂ := y) (transport i L t v x y a h).hom g x' y' hx hy =
      (transport i L t v x' y' a' h').hom := by
  apply ScaledFiberIsomorphisms.rescale_natural L
    (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x y a h) g x' y' hx hy
    (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x' y' a' h') (v T a)⁻¹ (v U a')⁻¹
  · exact Subgroup.TranslationFibers.transport_natural i L (NormalizedTranslationUnit.translation i L t) g x y a h x' y' a' h' hx hy ha
  · let φ : Γ(T.left, ⊤)ˣ →* Γ(U.left, ⊤)ˣ := Units.map g.left.appTop.hom.toMonoidHom
    exact (map_inv φ (v T a)).trans (congrArg Inv.inv hv)

/-- The regular cocycle splitting equation gives exact composition of actual corrected transports. -/
theorem comp {T : Over (Spec (.of k))} (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z)
    (hc : a * b = c)
    (hv : Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) a b * v T c = v T a * v T b) :
    transport i L t v x y a hx ≪≫ transport i L t v y z b hy = transport i L t v x z c hz := by
  apply ScaledLineIsomorphisms.corrected_comp (FiberIsomorphismRatios.fiberLine L x)
    (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x y a hx)
    (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) y z b hy)
    (Subgroup.TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x z c hz) (v T a) (v T b) (v T c)
  exact (congrArg (fun r => r * v T c)
    (Subgroup.DefectCocycle.defect_eq_parameter i L (NormalizedTranslationUnit.translation i L t)
      x y z a b c hx hy hz hc)).trans hv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CorrectedSubgroupTransport
