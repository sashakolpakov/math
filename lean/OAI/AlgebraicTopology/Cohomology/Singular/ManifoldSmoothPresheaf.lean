import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Homology.Functor

/-! # Manifold Smooth Presheaf -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf

noncomputable section

/-!
# Smooth singular cochains on open subsets of a manifold

Each open subset carries its actual induced charted-space structure. Inclusions
of open subsets are smooth, and therefore induce maps of the genuine smooth
singular simplicial sets. Pulling back cochains gives the presheaf constructed
here. No sheaf condition is asserted for ordinary smooth singular cochains.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- Smooth singular simplicial sets of open subsets, covariant for inclusions. -/
def manifoldOpenSmoothSingularFunctor : Opens M ⥤ SSet.{0} where
  obj U := (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
  map i := ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Opens.inclusion i.le) (contMDiff_inclusion i.le)
  map_id U := by
    ext n σ
    apply Subtype.ext
    rfl
  map_comp i j := by
    ext n σ
    apply Subtype.ext
    rfl

/-- Forgetting smoothness is natural over all open subsets. -/
def manifoldOpenSmoothInclusion :
    manifoldOpenSmoothSingularFunctor E M ⟶ (Opens.toTopCat (TopCat.of M)) ⋙ TopCat.toSSet where
  app U := ManifoldSmooth.manifoldSmoothInclusion E U
  naturality _ _ i :=
    ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion (Opens.inclusion i.le) (contMDiff_inclusion i.le)

variable {R : Type} [Ring R]

/-- The actual presheaf of smooth singular cochain complexes on a charted manifold. -/
def manifoldSmoothCochainPresheaf (A : ModuleCat.{0} R) :
    (TopCat.of M).Presheaf (CochainComplex (ModuleCat.{0} R) ℕ) :=
  (manifoldOpenSmoothSingularFunctor E M).op ⋙ Singular.Functor.simplicialCochainsFunctor A

/-- Cochain restriction along an inclusion of open subsets. -/
def manifoldSmoothOpenRestriction (A : ModuleCat.{0} R) {U V : Opens M} (i : U ⟶ V) :
    ManifoldSmooth.manifoldSmoothCochains E A V ⟶ ManifoldSmooth.manifoldSmoothCochains E A U :=
  Singular.Functor.simplicialPullback A ((manifoldOpenSmoothSingularFunctor E M).map i)

@[simp]
theorem manifoldSmoothCochainPresheaf_obj (A : ModuleCat.{0} R) (U : Opens M) :
    (manifoldSmoothCochainPresheaf E M A).obj (op U) = ManifoldSmooth.manifoldSmoothCochains E A U := rfl

/-- The presheaf restriction is exactly pullback along the actual smooth inclusion. -/
@[simp]
theorem manifoldSmoothCochainPresheaf_map (A : ModuleCat.{0} R)
    {U V : Opens M} (i : U ⟶ V) :
    (manifoldSmoothCochainPresheaf E M A).map i.op =
      manifoldSmoothOpenRestriction E M A i := rfl

@[simp]
theorem manifoldSmoothOpenRestriction_id (A : ModuleCat.{0} R) (U : Opens M) :
    manifoldSmoothOpenRestriction E M A (𝟙 U) = 𝟙 (ManifoldSmooth.manifoldSmoothCochains E A U) :=
  (manifoldSmoothCochainPresheaf E M A).map_id (op U)

@[simp]
theorem manifoldSmoothOpenRestriction_comp (A : ModuleCat.{0} R)
    {U V W : Opens M} (i : U ⟶ V) (j : V ⟶ W) :
    manifoldSmoothOpenRestriction E M A (i ≫ j) =
      manifoldSmoothOpenRestriction E M A j ≫ manifoldSmoothOpenRestriction E M A i :=
  (manifoldSmoothCochainPresheaf E M A).map_comp j.op i.op

/-- Restriction commutes with every cochain differential. -/
theorem manifoldSmoothOpenRestriction_comm (A : ModuleCat.{0} R)
    {U V : Opens M} (i : U ⟶ V) (n m : ℕ) :
    (manifoldSmoothOpenRestriction E M A i).f n ≫ (ManifoldSmooth.manifoldSmoothCochains E A U).d n m =
      (ManifoldSmooth.manifoldSmoothCochains E A V).d n m ≫ (manifoldSmoothOpenRestriction E M A i).f m :=
  (manifoldSmoothOpenRestriction E M A i).comm n m

/-- The module-valued smooth singular cochain presheaf in a fixed degree. -/
def manifoldSmoothCochainDegreePresheaf (A : ModuleCat.{0} R) (n : ℕ) :
    (TopCat.of M).Presheaf (ModuleCat.{0} R) :=
  manifoldSmoothCochainPresheaf E M A ⋙
    HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- The presheaf of smooth singular cohomology groups. -/
def manifoldSmoothCohomologyPresheaf (A : ModuleCat.{0} R) (n : ℕ) :
    (TopCat.of M).Presheaf (ModuleCat.{0} R) :=
  manifoldSmoothCochainPresheaf E M A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

@[simp]
theorem manifoldSmoothCochainDegreePresheaf_obj (A : ModuleCat.{0} R)
    (U : Opens M) (n : ℕ) :
    (manifoldSmoothCochainDegreePresheaf E M A n).obj (op U) =
      (ManifoldSmooth.manifoldSmoothCochains E A U).X n := rfl

@[simp]
theorem manifoldSmoothCohomologyPresheaf_obj (A : ModuleCat.{0} R)
    (U : Opens M) (n : ℕ) :
    (manifoldSmoothCohomologyPresheaf E M A n).obj (op U) =
      (ManifoldSmooth.manifoldSmoothCochains E A U).homology n := rfl

/-- The cochain complex of module-valued presheaves obtained degree by degree. -/
def manifoldSmoothPresheafComplex (A : ModuleCat.{0} R) :
    CochainComplex ((Opens M)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ where
  X := manifoldSmoothCochainDegreePresheaf E M A
  d i j :=
    { app := fun U => ((manifoldSmoothCochainPresheaf E M A).obj U).d i j
      naturality := fun U V f => ((manifoldSmoothCochainPresheaf E M A).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext U
    exact ((manifoldSmoothCochainPresheaf E M A).obj U).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact ((manifoldSmoothCochainPresheaf E M A).obj U).d_comp_d i j k

@[simp]
theorem manifoldSmoothPresheafComplex_d_app (A : ModuleCat.{0} R)
    (U : Opens M) (i j : ℕ) :
    ((manifoldSmoothPresheafComplex E M A).d i j).app (op U) =
      (ManifoldSmooth.manifoldSmoothCochains E A U).d i j := rfl

/-- Restriction from continuous to smooth singular cochains on all open subsets. -/
def manifoldSmoothRestrictionNatTrans (A : ModuleCat.{0} R) :
    (Opens.toTopCat (TopCat.of M)).op ⋙ Singular.Functor.singularCochainsFunctor A ⟶
      manifoldSmoothCochainPresheaf E M A where
  app U := ManifoldSmooth.manifoldSmoothCochainRestriction E A U.unop
  naturality _ _ f := by
    exact ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
      (Opens.inclusion f.unop.le)
      (contMDiff_inclusion (I := 𝓘(ℝ, E)) f.unop.le)

@[simp]
theorem manifoldSmoothRestrictionNatTrans_app (A : ModuleCat.{0} R) (U : Opens M) :
    (manifoldSmoothRestrictionNatTrans E M A).app (op U) =
      ManifoldSmooth.manifoldSmoothCochainRestriction E A U := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf
