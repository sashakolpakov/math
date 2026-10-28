import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

/-! # Finite Germ Gluing -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.FiniteGermGluing

noncomputable section

/-!
# A global singular cochain realizing finite compatible germ data

Singular cochains are arbitrary functions on genuine continuous simplices.
A finite open shrinking therefore permits a global cochain to realize
compatible local germs: choose a containing member of the shrinking for
each small simplex, and assign zero to the remaining simplices. Finiteness
allows one common neighborhood to verify the resulting germ at a point.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

open OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

variable {R : Type} [Ring R]

/-- Function coordinates for actual singular cochains on an open subspace. -/
abbrev singularOpenCochainFunctions (M : ModuleCat.{0} R) (X : TopCat.{0})
    (n : ℕ) (U : Opens X) :
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).obj (op U) ≅
      ModuleCat.of R (C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) → M) :=
  Coefficients.singularDegreewiseContinuousFunctionIso M (TopCat.of U) n

/-- In these function coordinates, presheaf restriction is simplex
postcomposition by the actual open-subspace inclusion. -/
theorem singularOpenCochainFunctions_restriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    (n : ℕ) {W U : Opens X} (f : W ⟶ U)
    (c : (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).obj (op U))
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), W)) :
    (singularOpenCochainFunctions M X n W).hom
        ((DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).map f.op c) σ =
      (singularOpenCochainFunctions M X n U).hom c
        (((Opens.toTopCat X).map f).hom.comp σ) :=
  ContinuousFormulas.singularDegreewiseContinuousFunctionIso_pullback M ((Opens.toTopCat X).map f) c σ

/-- A continuous singular simplex whose image lies in an open set,
regarded as an actual simplex of that open subspace. -/
def singularSimplexCodRestrict (X : TopCat.{0}) (n : ℕ) (U : Opens X)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) (hσ : Set.range σ ⊆ U) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) where
  toFun t := ⟨σ t, hσ ⟨t, rfl⟩⟩
  continuous_toFun := σ.continuous.subtype_mk _

/-- A point has a neighborhood meeting only those members of a finite
family whose closures contain the point. -/
theorem exists_open_nhds_detecting_finite_closures {ι : Type} [Finite ι]
    (X : TopCat.{0}) (V : ι → Opens X) (x : X) :
    ∃ W : Opens X, x ∈ W ∧
      ∀ i, ((W : Set X) ∩ (V i : Set X)).Nonempty → x ∈ closure (V i : Set X) := by
  classical
  let N : ι → Opens X := fun i =>
    if x ∈ closure (V i : Set X) then ⊤
    else ⟨(closure (V i : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨⨅ i, N i, ?_, ?_⟩
  · change x ∈ ((⨅ i, N i : Opens X) : Set X)
    rw [Opens.coe_iInf]
    apply Set.mem_iInter.mpr
    intro i
    dsimp only [N]
    split_ifs with h
    · trivial
    · exact h
  · intro i hi
    by_contra hx
    obtain ⟨y, hy, hyV⟩ := hi
    have hyN : y ∈ N i := (iInf_le N i : (⨅ i, N i) ≤ N i) hy
    dsimp only [N] at hyN
    rw [ite_eq_right hx] at hyN
    exact hyN (subset_closure hyV)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A finite open shrinking and compatible actual cochain germs give an
actual global singular cochain with precisely those germs. No compactness
or sheaf axiom is assumed. -/
theorem exists_global_singularCochain_of_finite_germ_compatible
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    {ι : Type} [Fintype ι] (U V : ι → Opens X)
    (hcover : iSup V = ⊤)
    (hVU : ∀ i, closure (V i : Set X) ⊆ (U i : Set X))
    (c : ∀ i, (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).obj (op (U i)))
    (hcompat : ∀ i j (x : X) (hxi : x ∈ U i) (hxj : x ∈ U j),
      (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).germ (U i) x hxi (c i) =
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).germ (U j) x hxj (c j)) :
    ∃ cglobal : (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).obj (op ⊤),
      ∀ i (x : X) (hxi : x ∈ U i),
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).germ ⊤ x (by trivial) cglobal =
          (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).germ (U i) x hxi (c i) := by
  classical
  let F := DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n
  have hsub (i : ι) : (V i : Set X) ⊆ (U i : Set X) :=
    subset_closure.trans (hVU i)
  let φ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M := fun σ =>
    if h : ∃ i, Set.range σ ⊆ (V i : Set X) then
      (singularOpenCochainFunctions M X n (U (Classical.choose h))).hom
        (c (Classical.choose h))
        (singularSimplexCodRestrict X n (U (Classical.choose h)) σ
          ((Classical.choose_spec h).trans (hsub (Classical.choose h))))
    else 0
  let a := (Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ
  let cglobal : F.obj (op ⊤) :=
    (Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X))).f n a
  have htopres (W : Opens X) (f : W ⟶ ⊤) :
      F.map f.op cglobal = (Functor.singularPullback M (Opens.inclusion' W)).f n a := by
    have h : Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X)) ≫
        Functor.singularPullback M ((Opens.toTopCat X).map f) =
        Functor.singularPullback M (Opens.inclusion' W) := by
      rw [← Functor.singularPullback_comp]
      rfl
    exact ConcreteCategory.congr_hom (congrArg (fun g => g.f n) h) a
  refine ⟨cglobal, ?_⟩
  intro i x hxi
  have hxcover : x ∈ (iSup V : Opens X) := by rw [hcover]; trivial
  have hxcover' : x ∈ ⋃ j, (V j : Set X) := by
    change x ∈ ((iSup V : Opens X) : Set X) at hxcover
    rw [Opens.coe_iSup] at hxcover
    exact hxcover
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxcover'
  have hxUj : x ∈ U j := hsub j hxj
  suffices hg : F.germ ⊤ x (by trivial) cglobal = F.germ (U j) x hxUj (c j) from
    hg.trans (hcompat j i x hxUj hxi)
  obtain ⟨N, hxN, hN⟩ := exists_open_nhds_detecting_finite_closures X V x
  have hlocal (k : ι) : ∃ W : Opens X, x ∈ W ∧
      ∀ hxk : x ∈ closure (V k : Set X),
        ∃ (f : W ⟶ U k) (g : W ⟶ U j), F.map f.op (c k) = F.map g.op (c j) := by
    by_cases hxk : x ∈ closure (V k : Set X)
    · obtain ⟨W, hxW, f, g, heq⟩ :=
        F.germ_eq x (hVU k hxk) hxUj (c k) (c j)
          (hcompat k j x (hVU k hxk) hxUj)
      exact ⟨W, hxW, fun _ => ⟨f, g, heq⟩⟩
    · exact ⟨⊤, by trivial, fun hxk' => (hxk hxk').elim⟩
  choose L hxL hL using hlocal
  let W : Opens X := V j ⊓ (N ⊓ iInf L)
  have hxAll : x ∈ (iInf L : Opens X) := by
    change x ∈ ((iInf L : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxL
  have hxW : x ∈ W := ⟨hxj, hxN, hxAll⟩
  have hWj : W ≤ V j := inf_le_left
  have hWN : W ≤ N := inf_le_right.trans inf_le_left
  have hWL (k : ι) : W ≤ L k := inf_le_right.trans (inf_le_right.trans (iInf_le L k))
  let wj : W ⟶ U j := homOfLE (hWj.trans (hsub j))
  apply F.germ_ext W hxW (homOfLE le_top) wj
  rw [htopres]
  apply (singularOpenCochainFunctions M X n W).toLinearEquiv.injective
  funext σ
  change (Coefficients.singularDegreewiseContinuousFunctionIso M (TopCat.of W) n).hom
      ((Functor.singularPullback M (Opens.inclusion' W)).f n
        ((Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ)) σ =
    (singularOpenCochainFunctions M X n W).hom (F.map wj.op (c j)) σ
  refine (ContinuousFormulas.continuousFunction_pullback M (Opens.inclusion' W) φ σ).trans ?_
  refine Eq.trans ?_ (singularOpenCochainFunctions_restriction M X n wj (c j) σ).symm
  let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) := (Opens.inclusion' W).hom.comp σ
  have hτW : Set.range τ ⊆ (W : Set X) := by
    rintro _ ⟨t, rfl⟩
    exact (σ t).property
  have hex : ∃ k, Set.range τ ⊆ (V k : Set X) := ⟨j, hτW.trans hWj⟩
  change φ τ = _
  dsimp only [φ]
  rw [dite_eq_left hex]
  let k := Classical.choose hex
  have hk : Set.range τ ⊆ (V k : Set X) := Classical.choose_spec hex
  let t₀ : Convexity.StdSimplex ℝ (Fin (n + 1)) :=
    Convexity.StdSimplex.single 0
  have hxk : x ∈ closure (V k : Set X) :=
    hN k ⟨τ t₀, hWN (hτW ⟨t₀, rfl⟩), hk ⟨t₀, rfl⟩⟩
  obtain ⟨f, g, heq⟩ := hL k hxk
  let wl : W ⟶ L k := homOfLE (hWL k)
  have heval := congrArg (fun z => (singularOpenCochainFunctions M X n (L k)).hom z
    (((Opens.toTopCat X).map wl).hom.comp σ)) heq
  have heval' := (singularOpenCochainFunctions_restriction M X n f (c k)
    (((Opens.toTopCat X).map wl).hom.comp σ)).symm.trans
      (heval.trans (singularOpenCochainFunctions_restriction M X n g (c j)
        (((Opens.toTopCat X).map wl).hom.comp σ)))
  have hleft : singularSimplexCodRestrict X n (U k) τ (hk.trans (hsub k)) =
      ((Opens.toTopCat X).map f).hom.comp
        (((Opens.toTopCat X).map wl).hom.comp σ) := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    rfl
  have hright : ((Opens.toTopCat X).map g).hom.comp
        (((Opens.toTopCat X).map wl).hom.comp σ) =
      ((Opens.toTopCat X).map wj).hom.comp σ := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    rfl
  rw [← hleft, hright] at heval'
  exact heval'

end

end OAI.AlgebraicTopology.Cohomology.Singular.FiniteGermGluing
