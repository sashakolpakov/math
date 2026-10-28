import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles

/-! # Frames Frame -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-!
# ChernClass: frames on sections of actual open subschemes

These linear equivalences come from the line bundle's actual local sheaf
isomorphisms. They will allow transition functions to be compared on different
ambient opens without introducing a cohomological compatibility hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

variable {X : Scheme} (M : X.Modules) (U : X.Opens)

/-- Restriction along an actual open-subscheme inclusion preserves the section scalar action. -/
theorem openRestriction_smul (W : U.toScheme.Opens)
    (r : Γ(X, U.ι ''ᵁ W)) (m : Γ(M, U.ι ''ᵁ W)) :
    (M.smul (U := U.ι ''ᵁ W) r).hom m =
      ((M.restrict U.ι).smul (U := W) (r : Γ(U.toScheme, W))).hom m := by
  have h := ConcreteCategory.congr_hom
    (Scheme.Modules.smul_restrictAppIso_inv U.ι M W r) m
  rw [Scheme.Opens.ι_appIso] at h
  exact h

/-- A genuine sheaf trivialization gives a linear frame on every subopen's sections. -/
def frameOnImage (e : M.restrict U.ι ≅ Line.Bundles.Construction.structureModule U.toScheme)
    (W : U.toScheme.Opens) :
    Γ(M, U.ι ''ᵁ W) ≃ₗ[Γ(X, U.ι ''ᵁ W)] Γ(X, U.ι ''ᵁ W) where
  toFun m := e.hom.app W m
  invFun r := e.inv.app W r
  left_inv m := by
    have h := congrArg (fun f : M.restrict U.ι ⟶ M.restrict U.ι => f.app W) e.hom_inv_id
    exact ConcreteCategory.congr_hom h m
  right_inv r := by
    have h := congrArg (fun f : Line.Bundles.Construction.structureModule U.toScheme ⟶ Line.Bundles.Construction.structureModule U.toScheme =>
      f.app W) e.inv_hom_id
    exact ConcreteCategory.congr_hom h r
  map_add' m n := (e.hom.app W).hom.map_add m n
  map_smul' r m := by
    convert e.hom.app_smul r m using 1 <;> try rfl
    exact congrArg (e.hom.app W) (openRestriction_smul M U W r m)

/-- The frame coordinates commute with the actual restrictions of module sections. -/
theorem frameOnImage_naturality
    (e : M.restrict U.ι ≅ Line.Bundles.Construction.structureModule U.toScheme)
    {V W : U.toScheme.Opens} (h : V ≤ W) (m : Γ(M, U.ι ''ᵁ W)) :
    frameOnImage M U e V
        (M.presheaf.map (homOfLE (U.ι.image_mono h)).op m) =
      X.presheaf.map (homOfLE (U.ι.image_mono h)).op (frameOnImage M U e W m) := by
  have hn := ConcreteCategory.congr_hom
    (e.hom.mapPresheaf.naturality (homOfLE h).op) m
  exact hn

/-- Transport frame coordinates along equality of open subsets. -/
def transportFrame {V W : X.Opens} (h : V = W)
    (e : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V)) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  h ▸ e

/-- Naturality survives the canonical transports along equal open sets. -/
theorem transportFrame_naturality {A B A' B' : X.Opens}
    (hA : A = A') (hB : B = B') (h : B ≤ A) (h' : B' ≤ A')
    (eA : Γ(M, A) ≃ₗ[Γ(X, A)] Γ(X, A))
    (eB : Γ(M, B) ≃ₗ[Γ(X, B)] Γ(X, B))
    (hn : ∀ m, eB (M.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (eA m)) (m : Γ(M, A')) :
    transportFrame M hB eB (M.presheaf.map (homOfLE h').op m) =
      X.presheaf.map (homOfLE h').op (transportFrame M hA eA m) := by
  subst A'
  subst B'
  exact hn m

theorem image_preimage_subopen {V : X.Opens} (h : V ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using inf_eq_right.mpr h

/-- A local sheaf trivialization gives a frame on every smaller ambient open. -/
def frameOnOpen (e : M.restrict U.ι ≅ Line.Bundles.Construction.structureModule U.toScheme)
    (V : X.Opens) (h : V ≤ U) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  transportFrame M (image_preimage_subopen U h) (frameOnImage M U e (U.ι ⁻¹ᵁ V))

/-- Ambient-open frame coordinates commute with actual module restrictions. -/
theorem frameOnOpen_naturality
    (e : M.restrict U.ι ≅ Line.Bundles.Construction.structureModule U.toScheme)
    {V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U)
    (m : Γ(M, W)) :
    frameOnOpen M U e V (hVW.trans hWU) (M.presheaf.map (homOfLE hVW).op m) =
      X.presheaf.map (homOfLE hVW).op (frameOnOpen M U e W hWU m) := by
  exact transportFrame_naturality M
    (image_preimage_subopen U hWU) (image_preimage_subopen U (hVW.trans hWU))
    (U.ι.image_mono (show U.ι ⁻¹ᵁ V ≤ U.ι ⁻¹ᵁ W from fun _ hx => hVW hx)) hVW
    (frameOnImage M U e (U.ι ⁻¹ᵁ W)) (frameOnImage M U e (U.ι ⁻¹ᵁ V))
    (fun m => frameOnImage_naturality M U e
      (show U.ι ⁻¹ᵁ V ≤ U.ι ⁻¹ᵁ W from fun _ hx => hVW hx) m) m

end Construction

end AlgebraicGeometry.DivisorClass.Chern.FramesFrame

namespace AlgebraicGeometry.DivisorClass.Chern
section

/-!
# ChernClass: transition units compatible with all ambient-open restrictions

The units are computed from the genuine linear frames of module sections.
Their restriction law is proved using the naturality of those frames.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace FramesFrame.Construction

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

end FramesFrame.Construction

open OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- The chosen actual sheaf frame, evaluated on any smaller ambient open. -/
def Line.Bundles.AlgebraicLineBundle.sectionFrame (x : X.carrier) (W : X.carrier.Opens) (h : W ≤ L.trivializingOpen x) :
    Γ(L.sheaf, W) ≃ₗ[Γ(X.carrier, W)] Γ(X.carrier, W) :=
  FramesFrame.Construction.frameOnOpen L.sheaf (L.trivializingOpen x) (L.trivialization x) W h

theorem Line.Bundles.AlgebraicLineBundle.sectionFrame_naturality (x : X.carrier) {V W : X.carrier.Opens}
    (hVW : V ≤ W) (hW : W ≤ L.trivializingOpen x) (m : Γ(L.sheaf, W)) :
    L.sectionFrame x V (hVW.trans hW) (L.sheaf.presheaf.map (homOfLE hVW).op m) =
      X.carrier.presheaf.map (homOfLE hVW).op (L.sectionFrame x W hW m) :=
  FramesFrame.Construction.frameOnOpen_naturality L.sheaf (L.trivializingOpen x) (L.trivialization x) hVW hW m

/-- Actual transition functions as units of the original scheme's section rings. -/
def Line.Bundles.AlgebraicLineBundle.ambientTransitionOn (x y : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    Γ(X.carrier, W)ˣ :=
  FramesFrame.Construction.frameTransitionUnit (L.sectionFrame x W hx) (L.sectionFrame y W hy)

theorem Line.Bundles.AlgebraicLineBundle.ambientTransitionOn_cocycle (x y z : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (hz : W ≤ L.trivializingOpen z) :
    L.ambientTransitionOn x y W hx hy * L.ambientTransitionOn y z W hy hz =
      L.ambientTransitionOn x z W hx hz :=
  FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _

theorem Line.Bundles.AlgebraicLineBundle.ambientTransitionOn_restrict (x y : X.carrier) {V W : X.carrier.Opens}
    (hVW : V ≤ W) (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    Units.map (X.carrier.presheaf.map (homOfLE hVW).op).hom.toMonoidHom
      (L.ambientTransitionOn x y W hx hy) =
        L.ambientTransitionOn x y V (hVW.trans hx) (hVW.trans hy) :=
  FramesFrame.Construction.frameTransitionUnit_map (X.carrier.presheaf.map (homOfLE hVW).op).hom
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (L.sectionFrame x W hx) (L.sectionFrame y W hy)
    (L.sectionFrame x V (hVW.trans hx)) (L.sectionFrame y V (hVW.trans hy))
    (L.sectionFrame_naturality x hVW hx) (L.sectionFrame_naturality y hVW hy)

end

/-!
# ChernClass: comparison of frames through an actual module-sheaf isomorphism

The isomorphism acts on genuine modules of sections. Mixed transition units
compare a frame of its source with a transported frame of its target.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace FramesFrame.Construction

variable {X : Scheme} {M N : X.Modules}

/-- A genuine module-sheaf isomorphism induces a linear equivalence on each open. -/
def moduleSheafSectionIso (e : M ≅ N) (U : X.Opens) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  toFun m := e.hom.app U m
  invFun n := e.inv.app U n
  left_inv m := ConcreteCategory.congr_hom
    (congrArg (fun f : M ⟶ M => f.app U) e.hom_inv_id) m
  right_inv n := ConcreteCategory.congr_hom
    (congrArg (fun f : N ⟶ N => f.app U) e.inv_hom_id) n
  map_add' m n := (e.hom.app U).hom.map_add m n
  map_smul' r m := e.hom.app_smul r m

theorem moduleSheafSectionIso_naturality (e : M ≅ N) {V U : X.Opens}
    (h : V ≤ U) (m : Γ(M, U)) :
    moduleSheafSectionIso e V (M.presheaf.map (homOfLE h).op m) =
      N.presheaf.map (homOfLE h).op (moduleSheafSectionIso e U m) :=
  ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE h).op) m

variable {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- Transporting both frames through the same module equivalence preserves the transition. -/
theorem frameTransitionUnit_precompose (q : A ≃ₗ[R] B) (e f : B ≃ₗ[R] R) :
    frameTransitionUnit (q.trans e) (q.trans f) = frameTransitionUnit e f := by
  apply Units.ext
  change e (q (q.symm (f.symm 1))) = e (f.symm 1)
  rw [q.apply_symm_apply]

/-- The square of source, target, and mixed transitions commutes. -/
theorem frameTransitionUnit_square (q : A ≃ₗ[R] B)
    (e f : A ≃ₗ[R] R) (e' f' : B ≃ₗ[R] R) :
    frameTransitionUnit e (q.trans e') * frameTransitionUnit e' f' =
      frameTransitionUnit e f * frameTransitionUnit f (q.trans f') := by
  rw [← frameTransitionUnit_precompose q e' f', frameTransitionUnit_cocycle,
    frameTransitionUnit_cocycle]

end FramesFrame.Construction

open OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L M : Line.Bundles.AlgebraicLineBundle X) (e : L.sheaf ≅ M.sheaf)

/-- A frame of the target sheaf transported to the source by the actual isomorphism. -/
def Line.Bundles.AlgebraicLineBundle.transportedSectionFrame (x : X.carrier) (U : X.carrier.Opens)
    (h : U ≤ M.trivializingOpen x) : Γ(L.sheaf, U) ≃ₗ[Γ(X.carrier, U)] Γ(X.carrier, U) :=
  (FramesFrame.Construction.moduleSheafSectionIso e U).trans (M.sectionFrame x U h)

theorem Line.Bundles.AlgebraicLineBundle.transportedSectionFrame_naturality (x : X.carrier) {V U : X.carrier.Opens}
    (hVU : V ≤ U) (hU : U ≤ M.trivializingOpen x) (m : Γ(L.sheaf, U)) :
    L.transportedSectionFrame M e x V (hVU.trans hU)
        (L.sheaf.presheaf.map (homOfLE hVU).op m) =
      X.carrier.presheaf.map (homOfLE hVU).op (L.transportedSectionFrame M e x U hU m) := by
  change M.sectionFrame x V _ (FramesFrame.Construction.moduleSheafSectionIso e V _) = _
  rw [FramesFrame.Construction.moduleSheafSectionIso_naturality, M.sectionFrame_naturality]
  rfl

/-- The actual regular unit comparing a source frame and a transported target frame. -/
def Line.Bundles.AlgebraicLineBundle.mixedTransitionOn (x y : X.carrier) (U : X.carrier.Opens)
    (hx : U ≤ L.trivializingOpen x) (hy : U ≤ M.trivializingOpen y) : Γ(X.carrier, U)ˣ :=
  FramesFrame.Construction.frameTransitionUnit (L.sectionFrame x U hx) (L.transportedSectionFrame M e y U hy)

theorem Line.Bundles.AlgebraicLineBundle.mixedTransitionOn_restrict (x y : X.carrier) {V U : X.carrier.Opens}
    (hVU : V ≤ U) (hx : U ≤ L.trivializingOpen x) (hy : U ≤ M.trivializingOpen y) :
    Units.map (X.carrier.presheaf.map (homOfLE hVU).op).hom.toMonoidHom
        (L.mixedTransitionOn M e x y U hx hy) =
      L.mixedTransitionOn M e x y V (hVU.trans hx) (hVU.trans hy) :=
  FramesFrame.Construction.frameTransitionUnit_map (X.carrier.presheaf.map (homOfLE hVU).op).hom
    (L.sheaf.presheaf.map (homOfLE hVU).op)
    (L.sectionFrame x U hx) (L.transportedSectionFrame M e y U hy)
    (L.sectionFrame x V (hVU.trans hx)) (L.transportedSectionFrame M e y V (hVU.trans hy))
    (L.sectionFrame_naturality x hVU hx) (L.transportedSectionFrame_naturality M e y hVU hy)

/-- A genuine sheaf isomorphism intertwines the regular transition units. -/
theorem Line.Bundles.AlgebraicLineBundle.mixedTransitionOn_square (x y x' y' : X.carrier) (U : X.carrier.Opens)
    (hx : U ≤ L.trivializingOpen x) (hy : U ≤ L.trivializingOpen y)
    (hx' : U ≤ M.trivializingOpen x') (hy' : U ≤ M.trivializingOpen y') :
    L.mixedTransitionOn M e x x' U hx hx' * M.ambientTransitionOn x' y' U hx' hy' =
      L.ambientTransitionOn x y U hx hy * L.mixedTransitionOn M e y y' U hy hy' :=
  FramesFrame.Construction.frameTransitionUnit_square (FramesFrame.Construction.moduleSheafSectionIso e U)
    (L.sectionFrame x U hx) (L.sectionFrame y U hy)
    (M.sectionFrame x' U hx') (M.sectionFrame y' U hy')

end AlgebraicGeometry.DivisorClass.Chern

end

end OAI
