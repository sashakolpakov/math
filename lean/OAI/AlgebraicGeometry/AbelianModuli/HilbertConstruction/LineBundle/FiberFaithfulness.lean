import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndFramedPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants

/-! # Fiber Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A rational fiber detects line-bundle endomorphisms on a connected reduced proper scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem Line.Bundles.LineBundle.endPullback_injective_of_appTop_injective (L : Line.Bundles.LineBundle Y) (f : X ⟶ Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf)
    (hf : Function.Injective f.appTop) :
    Function.Injective (fun φ : End L.sheaf => (Scheme.Modules.pullback f).map φ) := by
  intro φ ψ h
  change (Scheme.Modules.pullback f).map φ = (Scheme.Modules.pullback f).map ψ at h
  apply L.endScalar_injective
  apply hf
  rw [L.endScalar_framed_pullback f φ e, L.endScalar_framed_pullback f ψ e, h]

theorem Line.Bundles.LineBundle.endPullback_atRationalPoint_injective {K : Type u} [Field K]
    (p : Y ⟶ Spec (.of K)) [UniversallyClosed p] [IsReduced Y] [ConnectedSpace Y]
    (x : Spec (.of K) ⟶ Y) (hx : x ≫ p = 𝟙 _) (L : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule (Spec (.of K)) ≅ (Scheme.Modules.pullback x).obj L.sheaf) :
    Function.Injective (fun φ : End L.sheaf => (Scheme.Modules.pullback x).map φ) := by
  let : IsIso x.appTop := (Proper.ConnectedReducedConstants.properConnectedReducedPointGlobalIso p x hx).isIso_inv
  exact L.endPullback_injective_of_appTop_injective x e (ConcreteCategory.bijective_of_isIso x.appTop).1

theorem Line.Bundles.LineBundle.iso_eq_of_pullback_eq {K : Type u} [Field K]
    (p : Y ⟶ Spec (.of K)) [UniversallyClosed p] [IsReduced Y] [ConnectedSpace Y]
    (x : Spec (.of K) ⟶ Y) (hx : x ≫ p = 𝟙 _) (L M : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule (Spec (.of K)) ≅ (Scheme.Modules.pullback x).obj L.sheaf)
    (a b : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback x).map a.hom = (Scheme.Modules.pullback x).map b.hom) : a = b := by
  have hab : a.hom ≫ b.inv = 𝟙 L.sheaf := by
    apply Line.Bundles.LineBundle.endPullback_atRationalPoint_injective p x hx L e
    change (Scheme.Modules.pullback x).map (a.hom ≫ b.inv) =
      (Scheme.Modules.pullback x).map (𝟙 L.sheaf)
    rw [Functor.map_comp, h, ← Functor.map_comp, b.hom_inv_id]
  apply Iso.ext
  apply (cancel_mono b.inv).mp
  exact hab.trans b.hom_inv_id.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
