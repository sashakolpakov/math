import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection

/-! # Intrinsic Smooth -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections

/-! Smooth sections on the actual ball with the C-infinity topology:
all real derivatives carry the compact-open topology simultaneously. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

theorem ballDomain_open : IsOpen Adelic.BallGeometryData.ballDomain := by
  apply isOpen_lt _ continuous_const
  exact (Complex.continuous_normSq.comp (continuous_apply 0)).add
    (Complex.continuous_normSq.comp (continuous_apply 1))

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

structure SmoothSection where
  value : Adelic.BallNatural.Ball → V
  smooth : Adelic.BallGeometryData.BallSmooth value

def extension (f : SmoothSection V) (z : IntrinsicExterior.Intrinsic.Tangent) : V :=
  if hz : z ∈ Adelic.BallGeometryData.ballDomain then f.value ⟨z, hz⟩ else 0

def derivative (f : SmoothSection V) (n : ℕ) :
    C(Adelic.BallNatural.Ball, ContinuousMultilinearMap ℝ (fun _ : Fin n => IntrinsicExterior.Intrinsic.Tangent) V) where
  toFun z := iteratedFDerivWithin ℝ n (extension V f) Adelic.BallGeometryData.ballDomain z.val
  continuous_toFun := (f.smooth.continuousOn_iteratedFDerivWithin (m := n) (by simp)
    ballDomain_open.uniqueDiffOn).domRestrict

/-- This induced topology is uniform convergence on compact subsets of
the ball for every derivative order, including the value at order zero. -/
instance : TopologicalSpace (SmoothSection V) :=
  TopologicalSpace.induced (fun f : SmoothSection V => fun n => derivative V f n) inferInstance

theorem derivative_continuous (n : ℕ) : Continuous (fun f : SmoothSection V => derivative V f n) :=
  by
    have h : Continuous (fun f : SmoothSection V => fun n => derivative V f n) :=
      continuous_induced_dom
    exact (continuous_apply n).comp h

variable {V} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def mapSection (L : V →L[ℝ] W) (f : SmoothSection V) : SmoothSection W where
  value z := L (f.value z)
  smooth := by
    have h := L.contDiff.comp_contDiffOn f.smooth
    apply h.congr
    intro z hz
    simp [hz]

def postcomposeDerivative (L : V →L[ℝ] W) (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => IntrinsicExterior.Intrinsic.Tangent) V →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => IntrinsicExterior.Intrinsic.Tangent) W :=
  ({ toFun := L.compContinuousMultilinearMap
     map_add' := by intro a b; ext u; simp
     map_smul' := by intro c a; ext u; simp } :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => IntrinsicExterior.Intrinsic.Tangent) V →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => IntrinsicExterior.Intrinsic.Tangent) W).mkContinuous ‖L‖
    (fun T => L.norm_compContinuousMultilinearMap_le T)

theorem derivative_map (L : V →L[ℝ] W) (f : SmoothSection V) (n : ℕ) :
    derivative W (mapSection L f) n =
      ContinuousMap.comp ⟨postcomposeDerivative L n, (postcomposeDerivative L n).continuous⟩
        (derivative V f n) := by
  have hext : extension W (mapSection L f) = L ∘ extension V f := by
    funext z
    by_cases hz : z ∈ Adelic.BallGeometryData.ballDomain <;> simp [extension, mapSection, hz]
  apply ContinuousMap.ext
  intro z
  change iteratedFDerivWithin ℝ n (extension W (mapSection L f)) Adelic.BallGeometryData.ballDomain z.val =
    L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ n (extension V f) Adelic.BallGeometryData.ballDomain z.val)
  rw [hext]
  exact L.iteratedFDerivWithin_comp_left (f.smooth z.val z.property)
    ballDomain_open.uniqueDiffOn z.property (by simp)

theorem mapSection_continuous (L : V →L[ℝ] W) : Continuous (mapSection L) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  have h := (ContinuousMap.continuous_postcomp ⟨postcomposeDerivative L n, (postcomposeDerivative L n).continuous⟩).comp
    (derivative_continuous V n)
  exact h.congr (fun f => (derivative_map L f n).symm)

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

def geometricSection (B : Adelic.DataTheta.ComparisonData F H K A) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) : SmoothSection (Adelic.DataTheta.TaylorTensor (A := A) 2) :=
  ⟨Adelic.DataTheta.geometricTensor B f 2, hTheta.2.2.2.2.2 f 2⟩

def topSection (B : Adelic.DataTheta.ComparisonData F H K A) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) : SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  mapSection ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).restrictScalars ℝ) (geometricSection B hTheta f)

theorem smooth_projection_continuous :
    Continuous (mapSection ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).restrictScalars ℝ)) :=
  mapSection_continuous _

theorem topSection_value (B : Adelic.DataTheta.ComparisonData F H K A) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (z : Adelic.BallNatural.Ball) :
    (topSection B hTheta f).value z = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z := rfl

end RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections

namespace RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicJoint

/-! Joint smoothness gives continuity in the native topology of all
derivatives on compact subsets. This analytic lemma will be applied to
explicit local period and determinant-frame coordinates. -/

open scoped ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections

theorem partial_iteratedFDeriv_smoothAt
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F → G} {x : E} {z : F}
    (h : ContDiffAt 𝕜 ∞ (Function.uncurry f) (x, z)) (a : ℕ) :
    ContDiffAt 𝕜 ∞ (fun w : E × F => iteratedFDeriv 𝕜 a (f w.1) w.2) (x, z) := by
  induction a with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using!
      h.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 𝕜 F G).symm : G →L[𝕜] F [×0]→L[𝕜] G)
  | succ a ih =>
    have hc : ContDiffAt 𝕜 ∞
        (fun w : (E × F) × F => iteratedFDeriv 𝕜 a (f w.1.1) w.2) ((x, z), z) :=
      ih.comp ((x, z), z) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt 𝕜 ∞
        (fun w : E × F => fderiv 𝕜 (iteratedFDeriv 𝕜 a (f w.1)) w.2) (x, z) :=
      hc.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Function.uncurry_def] using!
      hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (a + 1) => F) G).symm :
          (F →L[𝕜] F [×a]→L[𝕜] G) →L[𝕜] F [×(a + 1)]→L[𝕜] G)

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {s : Set E} (hs : IsOpen s) (f : E → IntrinsicExterior.Intrinsic.Tangent → V)
variable (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) (s ×ˢ Adelic.BallGeometryData.ballDomain))

include hf in
theorem slice_contDiff (p : s) : ContDiffOn ℝ ⊤ (f p.val) Adelic.BallGeometryData.ballDomain := by
  exact hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨p.property,hz⟩)

def jointSection (p : s) : IntrinsicSections.SmoothSection V where
  value z := f p.val z.val
  smooth := by
    apply (slice_contDiff f hf p).congr
    intro z hz
    exact dite_eq_left hz

theorem jointSection_derivative (p : s) (z : Adelic.BallNatural.Ball) (n : ℕ) :
    IntrinsicSections.derivative V (jointSection f hf p) n z = iteratedFDeriv ℝ n (f p.val) z.val := by
  change iteratedFDerivWithin ℝ n (IntrinsicSections.extension V (jointSection f hf p)) Adelic.BallGeometryData.ballDomain z.val = _
  have he : Set.EqOn (IntrinsicSections.extension V (jointSection f hf p)) (f p.val) Adelic.BallGeometryData.ballDomain := by
    intro w hw
    simp [IntrinsicSections.extension,jointSection,hw]
  rw [iteratedFDerivWithin_congr (𝕜 := ℝ) (s := Adelic.BallGeometryData.ballDomain) he
    (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property) n]
  exact iteratedFDerivWithin_eq_iteratedFDeriv IntrinsicSections.ballDomain_open.uniqueDiffOn
    (((slice_contDiff f hf p).contDiffAt (IntrinsicSections.ballDomain_open.mem_nhds z.property)).of_le (by simp)) z.property

include hs in
theorem jointSection_continuous : Continuous (jointSection f hf) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hcont : Continuous (fun q : s × Adelic.BallNatural.Ball => iteratedFDeriv ℝ n (f q.1.val) q.2.val) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have h : ContDiffAt ℝ ⊤ (Function.uncurry f) (q.1.val,q.2.val) :=
      hf.contDiffAt ((hs.prod IntrinsicSections.ballDomain_open).mem_nhds
        ⟨q.1.property,show q.2.val ∈ Adelic.BallGeometryData.ballDomain from q.2.property⟩)
    have hd : ContinuousAt
        (fun w : E × IntrinsicExterior.Intrinsic.Tangent => iteratedFDeriv ℝ n (f w.1) w.2) (q.1.val,q.2.val) :=
      (partial_iteratedFDeriv_smoothAt (f := f) (h.of_le (by simp)) n).continuousAt
    have hi : ContinuousAt (fun r : s × Adelic.BallNatural.Ball => (r.1.val,r.2.val)) q :=
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)).continuousAt
    exact ContinuousAt.comp (f := fun r : s × Adelic.BallNatural.Ball => (r.1.val,r.2.val)) (x := q) hd hi
  apply hcont.congr
  intro q
  exact (jointSection_derivative f hf q.1 q.2 n).symm

end RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicJoint

namespace RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicLocal

/-! Ambient regularity at every parameter/ball pair gives continuity
in the native C-infinity topology even when the parameter set is not open. -/

open scoped ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicJoint

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (s : Set E) (f : E → IntrinsicExterior.Intrinsic.Tangent → V)
variable (hf : ∀ p ∈ s, ∀ z ∈ Adelic.BallGeometryData.ballDomain, ContDiffAt ℝ ⊤ (Function.uncurry f) (p,z))

include hf in
theorem local_slice_analytic (p : s) (z : IntrinsicExterior.Intrinsic.Tangent) (hz : z ∈ Adelic.BallGeometryData.ballDomain) :
    ContDiffAt ℝ ⊤ (f p.val) z :=
  (hf p.val p.property z hz).comp z (contDiffAt_const.prodMk contDiffAt_id)

def localSection (p : s) : IntrinsicSections.SmoothSection V where
  value z := f p.val z.val
  smooth := by
    have hs : ContDiffOn ℝ ⊤ (f p.val) Adelic.BallGeometryData.ballDomain :=
      fun z hz => (local_slice_analytic s f hf p z hz).contDiffWithinAt
    apply hs.congr
    intro z hz
    exact dite_eq_left hz

theorem localSection_derivative (p : s) (z : Adelic.BallNatural.Ball) (n : ℕ) :
    IntrinsicSections.derivative V (localSection s f hf p) n z = iteratedFDeriv ℝ n (f p.val) z.val := by
  change iteratedFDerivWithin ℝ n (IntrinsicSections.extension V (localSection s f hf p)) Adelic.BallGeometryData.ballDomain z.val = _
  have he : Set.EqOn (IntrinsicSections.extension V (localSection s f hf p)) (f p.val) Adelic.BallGeometryData.ballDomain := by
    intro w hw
    simp [IntrinsicSections.extension,localSection,hw]
  rw [iteratedFDerivWithin_congr (𝕜 := ℝ) (s := Adelic.BallGeometryData.ballDomain) he
    (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property) n]
  exact iteratedFDerivWithin_eq_iteratedFDeriv IntrinsicSections.ballDomain_open.uniqueDiffOn
    ((local_slice_analytic s f hf p z.val z.property).of_le (by simp)) z.property

theorem localSection_continuous : Continuous (localSection s f hf) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hcont : Continuous (fun q : s × Adelic.BallNatural.Ball => iteratedFDeriv ℝ n (f q.1.val) q.2.val) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hd : ContinuousAt
        (fun w : E × IntrinsicExterior.Intrinsic.Tangent => iteratedFDeriv ℝ n (f w.1) w.2) (q.1.val,q.2.val) :=
      (IntrinsicJoint.partial_iteratedFDeriv_smoothAt (f := f)
        ((hf q.1.val q.1.property q.2.val q.2.property).of_le (by simp)) n).continuousAt
    have hi : ContinuousAt (fun r : s × Adelic.BallNatural.Ball => (r.1.val,r.2.val)) q :=
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)).continuousAt
    exact ContinuousAt.comp (f := fun r : s × Adelic.BallNatural.Ball => (r.1.val,r.2.val)) (x := q) hd hi
  apply hcont.congr
  intro q
  exact (localSection_derivative s f hf q.1 q.2 n).symm

end RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicLocal

end

end OAI
