import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

/-! # Separation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Separation.CrystallineAdapter

noncomputable section

/-! The actual Witt-base morphisms satisfy the separation hypothesis for global comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

instance wittStructureSeparated (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom] :
    IsSeparated (IntegralComparison.Witt.Crystalline.wittStructureMap p k X) := by
  unfold IntegralComparison.Witt.Crystalline.wittStructureMap
  infer_instance

theorem specialFiberSeparated {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq) :
    IsSeparated (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) := by
  have : IsProper A.specialFiber.scheme.hom := A.specialFiber.proper
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Separation.CrystallineAdapter
