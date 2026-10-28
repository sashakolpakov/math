import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTraceBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisStructureTrace
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Finite Flat Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiniteFlatTrace

noncomputable section

/-! An actual normalized structure-sheaf trace for every finite flat map of constant invertible degree over a locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X]
variable (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ} (hn : ∀ x, f.finrank x = n)

def locallyNoetherianFiniteFlatStructureTrace (u : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶ Line.Bundles.structureModule X :=
  Affine.BasisStructureTrace.affineBasisStructureTrace f (Subtype.val : Finite.FlatTraceBasis.FiniteFlatTraceOpen f n → X.Opens)
    (fun i => i.property.1) (fun i => i.property.1.preimage f)
    (fun i => i.property.2.some) u (Finite.FlatTraceBasis.finiteFlatTraceOpen_isBasis f hn)

theorem locallyNoetherianFiniteFlatStructureTrace_unit
    (u : Γ(X, ⊤)ˣ) (hu : (u : Γ(X, ⊤)) = n) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      locallyNoetherianFiniteFlatStructureTrace f hn u = 𝟙 (Line.Bundles.structureModule X) :=
  Affine.BasisStructureTrace.affineBasisStructureTrace_unit f _ _ _ _ u _ hu

include hn in
theorem locallyNoetherianFiniteFlat_structureUnit_splitMono
    (u : Γ(X, ⊤)ˣ) (hu : (u : Γ(X, ⊤)) = n) :
    IsSplitMono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
  ⟨⟨locallyNoetherianFiniteFlatStructureTrace f hn u,
    locallyNoetherianFiniteFlatStructureTrace_unit f hn u hu⟩⟩

include hn in
theorem locallyNoetherianFiniteFlat_pullbackStructureUnit_splitMono
    (u : Γ(X, ⊤)ˣ) (hu : (u : Γ(X, ⊤)) = n) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule X)) := by
  refine ⟨⟨(Scheme.Modules.pushforward f).map (Line.Bundles.structureModulePullbackIso f).hom ≫
    locallyNoetherianFiniteFlatStructureTrace f hn u, ?_⟩⟩
  rw [← Category.assoc, Tensor.PullbackUnits.structureModulePullbackIso_unit]
  exact locallyNoetherianFiniteFlatStructureTrace_unit f hn u hu

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiniteFlatTrace
