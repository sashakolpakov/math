import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf

/-! # Compatible Frame Local -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleFrameLocal

noncomputable section

/-! Images of local frames in an arbitrary actual module sheaf, with restriction and transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

structure CompatibleFrameImages (D : OpenFrame.Transitions.OpenFrameTransitions U) (N : X.Modules) where
  value : ∀ (V : X.Opens) (i : ι), V ≤ U i → Γ(N, V)
  restrict : ∀ (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ U i),
    N.presheaf.map (homOfLE h).op (value V i hi) = value W i (h.trans hi)
  change : ∀ (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j),
    value V j hj = (D.value V i j hi hj).val • value V i hi

namespace CompatibleFrameImages

variable {D : OpenFrame.Transitions.OpenFrameTransitions U} {M N : X.Modules}
variable (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleFrameImages D N)

def localMap (V : X.Opens) (i : ι) (hi : V ≤ U i) : Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) :=
  ((LinearMap.id : Γ(X, V) →ₗ[Γ(X, V)] Γ(X, V)).smulRight (F.value V i hi)).comp
    (E.frame V i hi).symm.toLinearMap

theorem localMap_independent (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    F.localMap E V i hi = F.localMap E V j hj := by
  apply LinearMap.ext
  intro x
  change (E.frame V i hi).symm x • F.value V i hi = (E.frame V j hj).symm x • F.value V j hj
  rw [E.coordinate_change V i j hi hj, F.change V i j hi hj, smul_smul, mul_comm]

theorem localMap_restrict (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : W ≤ U i) (hj : V ≤ U j) (x : Γ(M, V)) :
    F.localMap E W i hi (M.presheaf.map (homOfLE h).op x) =
      N.presheaf.map (homOfLE h).op (F.localMap E V j hj x) := by
  have he := LinearMap.congr_fun (F.localMap_independent E W i j hi (h.trans hj))
    (M.presheaf.map (homOfLE h).op x)
  have hc := E.coordinate_restrict V W h j hj x
  have hv := F.restrict V W h j hj
  exact he.trans ((congrArg₂ (fun r : Γ(X, W) => fun s : Γ(N, W) => r • s) hc hv.symm).trans
    (Scheme.Modules.map_smul N (homOfLE h) ((E.frame V j hj).symm x) (F.value V j hj)).symm)

end CompatibleFrameImages

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleFrameLocal
