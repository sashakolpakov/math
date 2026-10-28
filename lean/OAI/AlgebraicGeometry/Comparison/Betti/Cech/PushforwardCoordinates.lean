import OAI.AlgebraicGeometry.Comparison.Betti.Module.CechFunctor
import Mathlib.Topology.Sheaves.Functors

/-! # Pushforward Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates

noncomputable section

/-! Čech cochains of a genuine presheaf direct image are cochains on the preimage cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

theorem cechIntersection_preimage {n : ℕ} (a : Fin (n + 1) → ι) :
    (Opens.map f).obj (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) =
      OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (Opens.map f).obj (U i)) a := by
  ext y
  change (f y ∈ OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ↔
    y ∈ OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (Opens.map f).obj (U i)) a
  simp only [OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection]
  rfl

variable (F : (Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ)

def cechPushforwardSectionIso {n : ℕ} (a : Fin (n + 1) → ι) :
    F.obj (op ((Opens.map f).obj (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) ≅
      F.obj (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (Opens.map f).obj (U i)) a)) :=
  F.mapIso (eqToIso (congrArg op (cechIntersection_preimage f U a)))

def cechPushforwardCoordinatesIso (n : ℕ) :
    ModuleCat.of ℂ (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.CechCochain ((Opens.map f).op ⋙ F) U n) ≅
      ModuleCat.of ℂ (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.CechCochain F (fun i => (Opens.map f).obj (U i)) n) :=
  (LinearEquiv.piCongrRight (fun a => (cechPushforwardSectionIso f U F a).toLinearEquiv)).toModuleIso

theorem cechPushforwardSectionIso_precomp {n m : SimplexCategory} (g : n ⟶ m)
    (a : Fin (m.len + 1) → ι) :
    F.map ((Opens.map f).map
      (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a g.toOrderHom))).op ≫
        (cechPushforwardSectionIso f U F a).hom =
      (cechPushforwardSectionIso f U F (a ∘ g.toOrderHom)).hom ≫
        F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp
          (fun i => (Opens.map f).obj (U i)) a g.toOrderHom)).op := by
  change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

def cechPushforwardCosimplicialIso :
    OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechCosimplicial ((Opens.map f).op ⋙ F) U ≅
      OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechCosimplicial F (fun i => (Opens.map f).obj (U i)) :=
  NatIso.ofComponents (fun n => cechPushforwardCoordinatesIso f U F n.len) (fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    exact ConcreteCategory.congr_hom (cechPushforwardSectionIso_precomp f U F g a)
      (x (a ∘ g.toOrderHom)))

def cechPushforwardComplexIso :
    OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechComplex ((Opens.map f).op ⋙ F) U ≅
      OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechComplex F (fun i => (Opens.map f).obj (U i)) :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{0} ℂ)).mapIso
    (cechPushforwardCosimplicialIso f U F)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates
