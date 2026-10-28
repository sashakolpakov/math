import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Frames

/-! # Frame Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-!
# LineBundleCycles: transition units compatible with all ambient-open restrictions

The units are computed from the genuine linear frames of module sections.
Their restriction law is proved using the naturality of those frames.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace LineBundle.FrameComparison.Cycles.LineBundleConstruction

variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

theorem rankOneLinearEquiv_apply (e : R ≃ₗ[R] R) (r : R) : e r = r * e 1 := by
  simpa only [smul_eq_mul, mul_one] using e.map_smul r 1

/-- An automorphism of a free rank-one module is multiplication by this unit. -/
def rankOneLinearEquivUnit (e : R ≃ₗ[R] R) : Rˣ where
  val := e 1
  inv := e.symm 1
  val_inv := by rw [← rankOneLinearEquiv_apply, e.symm_apply_apply]
  inv_val := by rw [← rankOneLinearEquiv_apply, e.apply_symm_apply]

theorem rankOneLinearEquivUnit_trans (e f : R ≃ₗ[R] R) :
    rankOneLinearEquivUnit (e.trans f) = rankOneLinearEquivUnit e * rankOneLinearEquivUnit f := by
  apply Units.ext
  exact rankOneLinearEquiv_apply f (e 1)

/-- Transition coordinates with `e(m) = g(e,f) * f(m)`.
Thus the generator belonging to `f` is `g(e,f)` times the generator belonging to `e`. -/
def frameTransitionUnit (e f : M ≃ₗ[R] R) : Rˣ :=
  rankOneLinearEquivUnit (f.symm.trans e)

theorem frameTransitionUnit_coordinates (e f : M ≃ₗ[R] R) (m : M) :
    e m = (frameTransitionUnit e f : R) * f m := by
  have h := rankOneLinearEquiv_apply (f.symm.trans e) (f m)
  change e m = e (f.symm 1) * f m
  simpa only [LinearEquiv.trans_apply, f.symm_apply_apply, mul_comm] using h

theorem frameTransitionUnit_cocycle (e f g : M ≃ₗ[R] R) :
    frameTransitionUnit e f * frameTransitionUnit f g = frameTransitionUnit e g := by
  unfold frameTransitionUnit
  rw [mul_comm, ← rankOneLinearEquivUnit_trans]
  congr 1
  ext r
  simp

/-- Compatibility of the frames with a restriction map forces compatibility of units. -/
theorem frameTransitionUnit_map (τ : R →+* S) (φ : M → N)
    (e f : M ≃ₗ[R] R) (e' f' : N ≃ₗ[S] S)
    (he : ∀ m, e' (φ m) = τ (e m)) (hf : ∀ m, f' (φ m) = τ (f m)) :
    Units.map τ.toMonoidHom (frameTransitionUnit e f) = frameTransitionUnit e' f' := by
  apply Units.ext
  change τ (e (f.symm 1)) = e' (f'.symm 1)
  have hm : φ (f.symm 1) = f'.symm 1 := by
    apply f'.injective
    rw [hf, f.apply_symm_apply, map_one, f'.apply_symm_apply]
  rw [← he, hm]

end LineBundle.FrameComparison.Cycles.LineBundleConstruction

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

/-- The chosen actual sheaf frame, evaluated on any smaller ambient open. -/
def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.sectionFrame (x : X) (W : X.Opens) (h : W ≤ L.trivializingOpen x) :
    Γ(L.sheaf, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  LineBundle.Frames.Cycles.LineBundleConstruction.frameOnOpen L.sheaf (L.trivializingOpen x) (L.trivialization x) W h

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.sectionFrame_naturality (x : X) {V W : X.Opens}
    (hVW : V ≤ W) (hW : W ≤ L.trivializingOpen x) (m : Γ(L.sheaf, W)) :
    L.sectionFrame x V (hVW.trans hW) (L.sheaf.presheaf.map (homOfLE hVW).op m) =
      X.presheaf.map (homOfLE hVW).op (L.sectionFrame x W hW m) :=
  LineBundle.Frames.Cycles.LineBundleConstruction.frameOnOpen_naturality L.sheaf (L.trivializingOpen x) (L.trivialization x) hVW hW m

/-- Actual transition functions as units of the original scheme's section rings. -/
def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.ambientTransitionOn (x y : X) (W : X.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    Γ(X, W)ˣ :=
  LineBundle.FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit (L.sectionFrame x W hx) (L.sectionFrame y W hy)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.ambientTransitionOn_cocycle (x y z : X) (W : X.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (hz : W ≤ L.trivializingOpen z) :
    L.ambientTransitionOn x y W hx hy * L.ambientTransitionOn y z W hy hz =
      L.ambientTransitionOn x z W hx hz :=
  LineBundle.FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_cocycle _ _ _

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.ambientTransitionOn_restrict (x y : X) {V W : X.Opens}
    (hVW : V ≤ W) (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    Units.map (X.presheaf.map (homOfLE hVW).op).hom.toMonoidHom
      (L.ambientTransitionOn x y W hx hy) =
        L.ambientTransitionOn x y V (hVW.trans hx) (hVW.trans hy) :=
  LineBundle.FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_map (X.presheaf.map (homOfLE hVW).op).hom
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (L.sectionFrame x W hx) (L.sectionFrame y W hy)
    (L.sectionFrame x V (hVW.trans hx)) (L.sectionFrame y V (hVW.trans hy))
    (L.sectionFrame_naturality x hVW hx) (L.sectionFrame_naturality y hVW hy)

end

/-! # LineBundleCycles: actual rank-one frame comparisons under identity, transport, and four-frame composition -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace LineBundle.FrameComparison.Cycles.LineBundleConstruction

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

theorem frameTransitionUnit_self (e : M ≃ₗ[R] R) : frameTransitionUnit e e = 1 := by
  apply Units.ext
  exact e.apply_symm_apply 1

theorem frameTransitionUnit_precompose (e : M ≃ₗ[R] N) (f g : N ≃ₗ[R] R) :
    frameTransitionUnit (e.trans f) (e.trans g) = frameTransitionUnit f g := by
  apply Units.ext
  change f (e (e.symm (g.symm 1))) = f (g.symm 1)
  rw [e.apply_symm_apply]

theorem frameTransitionUnit_four (e f g h : M ≃ₗ[R] R) :
    frameTransitionUnit e f * frameTransitionUnit f g =
      frameTransitionUnit e h * frameTransitionUnit h g :=
  (frameTransitionUnit_cocycle e f g).trans (frameTransitionUnit_cocycle e h g).symm

end LineBundle.FrameComparison.Cycles.LineBundleConstruction

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.ambientTransitionOn_self {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (x : X) (W : X.Opens) (hW : W ≤ L.trivializingOpen x) : L.ambientTransitionOn x x W hW hW = 1 :=
  LineBundle.FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_self _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
