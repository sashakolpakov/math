import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphAmpleFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionPoincarePoint

/-! # Graph Fiber Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical Poincare graph bundle of a positive polarization is ample on every geometric fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

theorem PolarizationData.PositiveOnGeometricFiber.graph_isAmple
    {D : Dual.Data.DualAbelianData A} {p : A.scheme ⟶ D.abelian.scheme} [IsMonHom p]
    {K : Type u} [Field K] [IsAlgClosed K] {f : Spec (.of K) ⟶ S}
    (h : PolarizationData.PositiveOnGeometricFiber D p K f) :
    ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (Limits.pullback.fst A.scheme.hom f)).IsAmple := by
  obtain ⟨L, hL, ⟨e₀⟩, ⟨e⟩⟩ := h
  let B := A.pullback f
  let D' := D.pullback f
  let p' := (Over.pullback f).map p
  have hp' : IsMonHom p' := inferInstanceAs (IsMonHom ((Over.pullback f).map p))
  let L₁ := L.pullback (fst B.scheme B.scheme).left
  let L₂ := L.pullback (snd B.scheme B.scheme).left
  let e' : (((D'.poincareAt p').tensor L₁).tensor L₂).sheaf ≅ (L.pullback μ[B.scheme].left).sheaf :=
    Tensor.ProductSheaf.tensorModuleCongr
      (Tensor.ProductSheaf.tensorModuleCongr (Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso D p f) (Iso.refl L₁.sheaf))
      (Iso.refl L₂.sheaf) ≪≫ e
  have hG := @Polarization.GraphAmpleFormula.polarizationGraph_isAmple_of_formula K _ g (A.pullback f) D' p' hp' L e₀ e' hL
  exact hG.of_iso (PoincareGraph.Bundles.poincareGraphBundle_baseChangeIso D p f)

theorem PolarizationData.Polarization.graphBundle_ample_geometricFiber {D : Dual.Data.DualAbelianData A} {δ : Fin g → ℕ}
    (p : PolarizationData.Polarization D δ) (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) :
    ((PoincareGraph.Bundles.poincareGraphBundle D p.isogeny.hom).pullback (Limits.pullback.fst A.scheme.hom f)).IsAmple :=
  (p.positive K f).graph_isAmple

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
