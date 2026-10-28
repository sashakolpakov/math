import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.FiniteGermGluing
import Mathlib.Topology.LocallyFinite

/-! # Locally Finite Germ Gluing -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.LocallyFiniteGermGluing

noncomputable section

/-!
# Actual singular cochain gluing over a locally finite shrinking

The global cochain assigns values to actual continuous singular simplices.
At each point, local finiteness reduces the germ verification to the finite
set of shrinking members whose closures contain that point. No compactness
or surjectivity of sheafification is assumed.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

variable {R : Type} [Ring R]

/-- Local finiteness gives a neighborhood meeting only shrinking members
whose closures contain the chosen point. -/
theorem exists_open_nhds_detecting_locallyFinite_closures {ι : Type}
    (X : TopCat.{0}) (V : ι → Opens X)
    (hV : LocallyFinite (fun i => (V i : Set X))) (x : X) :
    ∃ W : Opens X, x ∈ W ∧
      ∀ i, ((W : Set X) ∩ (V i : Set X)).Nonempty →
        x ∈ closure (V i : Set X) := by
  have hnhds := hV.closure.iInter_compl_mem_nhds (fun _ => isClosed_closure) x
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp hnhds
  refine ⟨⟨W, hWo⟩, hxW, ?_⟩
  intro i hi
  by_contra hxi
  obtain ⟨y, hyW, hyV⟩ := hi
  have hy := Set.mem_iInter.mp (Set.mem_iInter.mp (hWsub hyW) i) hxi
  exact hy (subset_closure hyV)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Compatible genuine singular-cochain germs over a locally finite open
shrinking are realized by one actual global singular cochain. -/
theorem exists_global_singularCochain_of_locallyFinite_germ_compatible
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    {ι : Type} (U V : ι → Opens X)
    (hcover : iSup V = ⊤) (hfinite : LocallyFinite (fun i => (V i : Set X)))
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
      (FiniteGermGluing.singularOpenCochainFunctions M X n (U (Classical.choose h))).hom
        (c (Classical.choose h))
        (FiniteGermGluing.singularSimplexCodRestrict X n (U (Classical.choose h)) σ
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
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxcover
  have hxUj : x ∈ U j := hsub j hxj
  suffices hg : F.germ ⊤ x (by trivial) cglobal = F.germ (U j) x hxUj (c j) from
    hg.trans (hcompat j i x hxUj hxi)
  obtain ⟨N, hxN, hN⟩ :=
    exists_open_nhds_detecting_locallyFinite_closures X V hfinite x
  let I : Type := {k : ι // x ∈ closure (V k : Set X)}
  have : Finite I := (hfinite.closure.point_finite x).to_subtype
  have hlocal (k : I) : ∃ W : Opens X, x ∈ W ∧
      ∃ (f : W ⟶ U k.1) (g : W ⟶ U j), F.map f.op (c k.1) = F.map g.op (c j) := by
    obtain ⟨W, hxW, f, g, heq⟩ := F.germ_eq x (hVU k.1 k.2) hxUj (c k.1) (c j)
      (hcompat k.1 j x (hVU k.1 k.2) hxUj)
    exact ⟨W, hxW, f, g, heq⟩
  choose L hxL f g hL using hlocal
  let W : Opens X := V j ⊓ (N ⊓ iInf L)
  have hxAll : x ∈ (iInf L : Opens X) := by
    change x ∈ ((iInf L : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxL
  have hxW : x ∈ W := ⟨hxj, hxN, hxAll⟩
  have hWj : W ≤ V j := inf_le_left
  have hWN : W ≤ N := inf_le_right.trans inf_le_left
  have hWL (k : I) : W ≤ L k := inf_le_right.trans (inf_le_right.trans (iInf_le L k))
  let wj : W ⟶ U j := homOfLE (hWj.trans (hsub j))
  apply F.germ_ext W hxW (homOfLE le_top) wj
  rw [htopres]
  apply (FiniteGermGluing.singularOpenCochainFunctions M X n W).toLinearEquiv.injective
  funext σ
  change (Coefficients.singularDegreewiseContinuousFunctionIso M (TopCat.of W) n).hom
      ((Functor.singularPullback M (Opens.inclusion' W)).f n
        ((Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ)) σ =
    (FiniteGermGluing.singularOpenCochainFunctions M X n W).hom (F.map wj.op (c j)) σ
  refine (ContinuousFormulas.continuousFunction_pullback M (Opens.inclusion' W) φ σ).trans ?_
  refine Eq.trans ?_ (FiniteGermGluing.singularOpenCochainFunctions_restriction M X n wj (c j) σ).symm
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
  let k' : I := ⟨k, hxk⟩
  let wl : W ⟶ L k' := homOfLE (hWL k')
  have heval := congrArg (fun z => (FiniteGermGluing.singularOpenCochainFunctions M X n (L k')).hom z
    (((Opens.toTopCat X).map wl).hom.comp σ)) (hL k')
  have heval' := (FiniteGermGluing.singularOpenCochainFunctions_restriction M X n (f k') (c k)
    (((Opens.toTopCat X).map wl).hom.comp σ)).symm.trans
      (heval.trans (FiniteGermGluing.singularOpenCochainFunctions_restriction M X n (g k') (c j)
        (((Opens.toTopCat X).map wl).hom.comp σ)))
  have hleft : FiniteGermGluing.singularSimplexCodRestrict X n (U k) τ (hk.trans (hsub k)) =
      ((Opens.toTopCat X).map (f k')).hom.comp
        (((Opens.toTopCat X).map wl).hom.comp σ) := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    rfl
  have hright : ((Opens.toTopCat X).map (g k')).hom.comp
        (((Opens.toTopCat X).map wl).hom.comp σ) =
      ((Opens.toTopCat X).map wj).hom.comp σ := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    rfl
  rw [← hleft, hright] at heval'
  exact heval'

end

end OAI.AlgebraicTopology.Cohomology.Singular.LocallyFiniteGermGluing
