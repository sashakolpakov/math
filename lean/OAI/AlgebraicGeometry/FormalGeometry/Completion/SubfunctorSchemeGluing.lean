import OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorChart
import Mathlib.AlgebraicGeometry.Sites.Representability

/-! # Subfunctor Scheme Gluing -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorSchemeGluing

noncomputable section

/-! A sheaf subfunctor of a scheme's points is represented by gluing
its actual monomorphic charts over an open cover of the scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

namespace Construction

universe u
variable {S : Scheme.{u}} (P : Subfunctor (yoneda.obj S)) (U : S.OpenCover.{u})
  (M : ∀ i, Over (U.X i)) [∀ i, Mono (M i).hom]
  (h : ∀ i (Z : Scheme.{u}) (j : Z ⟶ U.X i),
    (j ≫ U.f i) ∈ P.obj (op Z) ↔ ∃ z : Z ⟶ (M i).left, z ≫ (M i).hom = j)

theorem subfunctorChartMap_isOpenImmersion (i : U.I₀) :
    IsOpenImmersion.presheaf (SubfunctorChart.Construction.subfunctorChartMap P (U.f i) (M i).hom (h i)) := by
  have : MorphismProperty.IsStableUnderBaseChange (@IsOpenImmersion).presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_isPullback (SubfunctorChart.Construction.subfunctorChart_isPullback P (U.f i) (M i).hom (h i))
    (MorphismProperty.relative_map (F := yoneda) (P := @IsOpenImmersion) inferInstance)

instance subfunctorChartMap_locallySurjective :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun i => SubfunctorChart.Construction.subfunctorChartMap P (U.f i) (M i).hom (h i))) where
  imageSieve_mem {Z} x := by
    apply Scheme.zariskiTopology.superset_covering _
      (Scheme.zariskiTopology.pullback_stable x.val U.mem_grothendieckTopology)
    intro W f hf
    obtain ⟨i, j, hj⟩ := (Sieve.mem_ofArrows_iff U.X U.f (f ≫ x.val)).mp hf
    have hp : (j ≫ U.f i) ∈ P.obj (op W) := hj ▸ P.map f.op x.property
    obtain ⟨z, hz⟩ := (h i W j).mp hp
    refine ⟨(Sigma.ι (fun i => yoneda.obj (M i).left) i).app (op W) z, ?_⟩
    have he := congrArg (fun t => t.app (op W))
      (Sigma.ι_comp_desc (fun i => SubfunctorChart.Construction.subfunctorChartMap P (U.f i) (M i).hom (h i)) i)
    have hv := ConcreteCategory.congr_hom he z
    refine hv.trans (Subtype.ext ?_)
    change z ≫ ((M i).hom ≫ U.f i) = f ≫ x.val
    rw [← Category.assoc, hz]
    exact hj.symm

include h in
theorem subfunctor_isRepresentable_of_openCover
    (hP : Presieve.IsSheaf Scheme.zariskiTopology P.toFunctor) : P.toFunctor.IsRepresentable := by
  let F : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨P.toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr hP⟩
  let g : ∀ i : U.I₀, yoneda.obj (M i).left ⟶ F.obj :=
    fun i => SubfunctorChart.Construction.subfunctorChartMap P (U.f i) (M i).hom (h i)
  have hg : ∀ i : U.I₀, IsOpenImmersion.presheaf (g i) :=
    fun i => subfunctorChartMap_isOpenImmersion P U M h i
  exact Scheme.LocalRepresentability.isRepresentable (F := F) (ι := U.I₀)
    (X := fun i => (M i).left) (f := g) hg

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorSchemeGluing
