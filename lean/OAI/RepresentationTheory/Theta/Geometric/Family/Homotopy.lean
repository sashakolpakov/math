import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Path

/-! # Homotopy -/

namespace OAI.RepresentationTheory.Theta.Geometric.Family.Homotopy

noncomputable section

/-! A path in the parameter space gives an actual homotopy between
the corresponding maps in a jointly continuous family. -/

variable {B T Y : Type} [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace Y]
    (f : C(B × T, Y))

def continuousFamilySlice (b : B) : C(T, Y) :=
  ⟨fun t => f (b, t), f.continuous.comp (continuous_const.prodMk continuous_id)⟩

def continuousFamilyHomotopy {b c : B} (p : Path b c) :
    ContinuousMap.Homotopy (continuousFamilySlice f b) (continuousFamilySlice f c) where
  toFun q := f (p q.1, q.2)
  continuous_toFun := f.continuous.comp ((p.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left := fun t => by change f (p 0, t) = f (b, t); rw [p.source]
  map_one_left := fun t => by change f (p 1, t) = f (c, t); rw [p.target]

theorem continuousFamily_homotopic {b c : B} (p : Path b c) :
    (continuousFamilySlice f b).Homotopic (continuousFamilySlice f c) :=
  ⟨continuousFamilyHomotopy f p⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Family.Homotopy
