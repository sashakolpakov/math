import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MaximalRank
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree

/-! # Finite Pullback -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback.Constructions.FiniteRank

/-!
# Nonzero holomorphic germs pull back along finite maps of equal dimension

If a pullback vanished on a neighborhood, a regular point of the finite map
would map a smaller neighborhood onto an open subset of the zero set. The
identity principle excludes this for a nonzero holomorphic germ.
-/

open Set Filter
open scoped _root_.Topology

theorem nonzero_germ_comp_of_finite_fibers
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hfinite : ∀ v : F, {y | y ∈ U ∧ f y = v}.Finite)
    {g : F → ℂ} {V : Set F} (hV : IsOpen V) (hg : DifferentiableOn ℂ g V)
    {x : E} (hx : x ∈ U) (hfx : f x ∈ V) (hgn : ¬∀ᶠ y in 𝓝 (f x), g y = 0) :
    ¬∀ᶠ y in 𝓝 x, g (f y) = 0 := by
  intro hzero
  obtain ⟨W, hW, hfxW, _, hdense⟩ :=
    GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hV hfx hg hgn
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ f y ∈ W ∧ g (f y) = 0 := by
    filter_upwards [hU.mem_nhds hx,
      (hf.differentiableAt (hU.mem_nhds hx)).continuousAt.eventually (hW.mem_nhds hfxW),
      hzero] with y hy hyW hyzero
    exact ⟨hy, hyW, hyzero⟩
  obtain ⟨U₀, hU₀sub, hU₀, hxU₀⟩ := mem_nhds_iff.mp hnear
  have hU₀U : U₀ ⊆ U := fun y hy => (hU₀sub hy).1
  obtain ⟨y, hy, hyD⟩ := MaximalRank.Constructions.FiniteRank.exists_injective_fderiv_of_finite_fibers hU₀ ⟨x, hxU₀⟩
    (hf.mono hU₀U) (fun v => (hfinite v).subset (fun _ hy => ⟨hU₀U hy.1, hy.2⟩))
  have hbij : Function.Bijective (fderiv ℂ f y) :=
    ⟨hyD, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hyD⟩
  let e := (LinearEquiv.ofBijective (fderiv ℂ f y).toLinearMap hbij).toContinuousLinearEquiv
  obtain ⟨q, hyq, hqf, _, _⟩ := HolomorphicRegularity.Constructions.Regularity.exists_holomorphic_localInverse hU₀ (hf.mono hU₀U) hy e rfl
  let O := q '' (q.source ∩ U₀)
  have hO : IsOpen O := q.isOpen_image_source_inter hU₀
  have hfyO : f y ∈ O := ⟨y, ⟨hyq, hy⟩, congrFun hqf y⟩
  have hfyW : f y ∈ W := (hU₀sub hy).2.1
  obtain ⟨z, hz, hzO⟩ := ((mem_closure_iff_frequently.mp (hdense hfyW)).and_eventually
    (hO.mem_nhds hfyO)).exists
  obtain ⟨w, hw, hwz⟩ := hzO
  have hfwz : f w = z := (congrFun hqf w).symm.trans hwz
  exact hz.2 (hfwz ▸ (hU₀sub hw.2).2.2)

end AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback.Constructions.FiniteRank

namespace AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback.Constructions.Cone

/-!
# Extending generic vanishing through finite holomorphic parametrizations

For an equal-dimensional finite holomorphic map, a nonzero exceptional
equation cannot pull back to the zero germ. Continuity therefore extends
vanishing from the generic fibers to every point in a local parametrization.
-/

open Set Filter
open scoped _root_.Topology

theorem eq_zero_of_generic_finite_parametrization
    {E A F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {S : Set A} (L : A →L[ℂ] F)
    (hfinite : ∀ v : F, {p | p ∈ S ∧ L p = v}.Finite)
    {U : Set E} (hU : IsOpen U) {φ : E → A} (hφ : DifferentiableOn ℂ φ U)
    (hmaps : MapsTo φ U S) (hinj : InjOn φ U)
    {V : Set F} (hV : IsOpen V) {c : F → ℂ} (hc : DifferentiableOn ℂ c V)
    {x : E} (hx : x ∈ U) (hLx : L (φ x) ∈ V)
    (hcn : ¬∀ᶠ y in 𝓝 (L (φ x)), c y = 0)
    {q : A → ℂ} (hq : ContinuousAt q (φ x))
    (hzero : ∀ p ∈ S, L p ∈ V → c (L p) ≠ 0 → q p = 0) : q (φ x) = 0 := by
  have hcomp : DifferentiableOn ℂ (fun y => L (φ y)) U :=
    L.differentiable.comp_differentiableOn hφ
  have hfib (v : F) : {y | y ∈ U ∧ L (φ y) = v}.Finite :=
    Set.Finite.of_injOn (f := φ) (s := {y | y ∈ U ∧ L (φ y) = v})
      (t := {p | p ∈ S ∧ L p = v}) (fun y hy => ⟨hmaps hy.1, hy.2⟩)
      (hinj.mono (fun _ hy => hy.1)) (hfinite v)
  have hnonzero := FiniteRank.nonzero_germ_comp_of_finite_fibers
    hdim hU hcomp hfib hV hc hx hLx hcn
  by_contra hn
  have hnearQ : ∀ᶠ y in 𝓝 x, q (φ y) ≠ 0 :=
    (hq.comp (hφ.differentiableAt (hU.mem_nhds hx)).continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds hn)
  have hnearV : ∀ᶠ y in 𝓝 x, L (φ y) ∈ V :=
    (hcomp.differentiableAt (hU.mem_nhds hx)).continuousAt.eventually (hV.mem_nhds hLx)
  apply hnonzero
  filter_upwards [hU.mem_nhds hx, hnearQ, hnearV] with y hy hyq hyV
  by_contra hcy
  exact hyq (hzero (φ y) (hmaps hy) hyV hcy)

theorem eq_zero_of_generic_finite_local_parametrizations
    {E A F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {S : Set A} (L : A →L[ℂ] F)
    (hfinite : ∀ v : F, {p | p ∈ S ∧ L p = v}.Finite)
    (hparam : ∀ p ∈ S, p ≠ 0 → ∃ (O : Set A) (U : Set E) (φ : E → A),
      IsOpen O ∧ p ∈ O ∧ IsOpen U ∧ DifferentiableOn ℂ φ U ∧
      S ∩ O ⊆ φ '' U ∧ MapsTo φ U S ∧ InjOn φ U)
    {p : A} (hp : p ∈ S) (hp0 : p ≠ 0)
    {V : Set F} (hV : IsOpen V) {c : F → ℂ} (hc : DifferentiableOn ℂ c V)
    (hLp : L p ∈ V) (hcn : ¬∀ᶠ y in 𝓝 (L p), c y = 0)
    {q : A → ℂ} (hq : ContinuousAt q p)
    (hzero : ∀ v ∈ S, L v ∈ V → c (L v) ≠ 0 → q v = 0) : q p = 0 := by
  obtain ⟨O, U, φ, _, hpO, hU, hφ, hsub, hmaps, hinj⟩ := hparam p hp hp0
  obtain ⟨x, hx, rfl⟩ := hsub ⟨hp, hpO⟩
  exact eq_zero_of_generic_finite_parametrization hdim L hfinite hU hφ hmaps hinj
    hV hc hx hLp hcn hq hzero

end AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback.Constructions.Cone

end

end OAI
