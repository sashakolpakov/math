import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.AlgebraicGeometry.GluingOneHypercover
import Mathlib.CategoryTheory.Sites.Over

/-! # Relative Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeGluing.Construction.Schemes

noncomputable section

/-!
# CartierDuality: gluing schemes over a fixed base
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Scheme gluing data in the category over a fixed base, with open
immersions as the overlap maps. -/
structure RelativeGlueData (S : Scheme.{u}) extends CategoryTheory.GlueData (Over S) where
  f_open : ∀ i j, IsOpenImmersion (f i j).left

attribute [instance] RelativeGlueData.f_open

namespace RelativeGlueData

variable {S : Scheme.{u}} (D : RelativeGlueData S)

instance forget_preservesOverlapPullbacks :
    ∀ i j k : D.J, PreservesLimit (cospan (D.f i j) (D.f i k)) (Over.forget S) :=
  fun _ _ _ => inferInstance

/-- Forgetting the base gives ordinary scheme gluing data. -/
def underlying : Scheme.GlueData where
  toGlueData := D.toGlueData.mapGlueData (Over.forget S)
  f_open := D.f_open

/-- The underlying relative gluing diagram has its scheme colimit. -/
instance underlyingDiagram_hasColimit :
    HasColimit (D.toGlueData.diagram.multispan ⋙ Over.forget S) := by
  let hmap : HasMulticoequalizer (D.toGlueData.mapGlueData (Over.forget S)).diagram :=
    inferInstanceAs (HasMulticoequalizer D.underlying.toGlueData.diagram)
  exact @hasColimit_of_iso _ _ _ _ _ _ hmap (D.toGlueData.diagramIso (Over.forget S))

/-- The gluing colimit exists over the base because the forgetful
functor creates colimits and the underlying scheme gluing exists. -/
instance : HasMulticoequalizer D.toGlueData.diagram :=
  hasColimit_of_created _ (Over.forget S)

/-- The glued scheme together with its descended map to the base. -/
abbrev glued : Over S := D.toGlueData.glued

/-- The underlying scheme is the ordinary scheme gluing. -/
def underlyingIso : D.glued.left ≅ D.underlying.glued :=
  D.toGlueData.gluedIso (Over.forget S)

/-- Each chart embeds openly into the glued relative scheme. -/
instance chart_isOpenImmersion (i : D.J) : IsOpenImmersion (D.toGlueData.ι i).left := by
  have h := D.toGlueData.ι_gluedIso_inv (Over.forget S) i
  change D.underlying.ι i ≫ D.underlyingIso.inv = (D.toGlueData.ι i).left at h
  rw [← h]
  let hι : IsOpenImmersion (D.underlying.ι i) :=
    Scheme.GlueData.ι_isOpenImmersion D.underlying i
  let : IsIso D.underlyingIso.inv := inferInstance
  let hinv : IsOpenImmersion D.underlyingIso.inv := IsOpenImmersion.of_isIso _
  exact @IsOpenImmersion.comp _ _ _ _ _ hι hinv

/-- The overlaps remain the scheme-theoretic intersections after gluing
in the relative category. -/
def overlapIsPullback (i j : D.J) : IsLimit (D.toGlueData.vPullbackCone i j) :=
  D.toGlueData.vPullbackConeIsLimitOfMap (Over.forget S) i j
    (D.underlying.vPullbackConeIsLimit i j)

/-- The relative charts cover the underlying glued scheme. -/
theorem charts_jointly_surjective (x : D.glued.left) :
    ∃ i y, (D.toGlueData.ι i).left y = x := by
  obtain ⟨i, y, hy⟩ := D.underlying.ι_jointly_surjective (D.underlyingIso.hom x)
  refine ⟨i, y, ?_⟩
  apply D.underlyingIso.hom.isOpenEmbedding.injective
  change ((D.toGlueData.ι i).left ≫ D.underlyingIso.hom) y = D.underlyingIso.hom x
  exact (congrArg (fun k => k y)
    (D.toGlueData.ι_gluedIso_hom (Over.forget S) i)).trans hy

/-- The glued relative charts form an open cover. -/
def openCover : Scheme.OpenCover D.glued.left where
  I₀ := D.J
  X i := (D.U i).left
  f i := (D.toGlueData.ι i).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨D.charts_jointly_surjective, inferInstance⟩

/-- The relative charts are a covering family in the slice Zariski site. -/
theorem charts_covering :
    Sieve.ofArrows D.U D.toGlueData.ι ∈ (Scheme.zariskiTopology.over S) D.glued := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact D.openCover.mem_grothendieckTopology

/-- The charts and their scheme-theoretic overlaps give a hypercover
of the relative gluing in the slice Zariski site. -/
def oneHypercover : (Scheme.zariskiTopology.over S).OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.toGlueData.ι
  I₁ _ _ := PUnit
  Y i j _ := D.V (i, j)
  p₁ i j _ := D.f i j
  p₂ i j _ := D.t i j ≫ D.f j i
  w i j _ := by simp only [Category.assoc, CategoryTheory.GlueData.glue_condition]
  mem₀ := by
    refine (Scheme.zariskiTopology.over S).superset_covering ?_ D.charts_covering
    rw [Sieve.generate_le_iff]
    rintro W _ ⟨i⟩
    exact ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩
  mem₁ i j W p q h := by
    refine (Scheme.zariskiTopology.over S).superset_covering (fun T g _ => ?_)
      ((Scheme.zariskiTopology.over S).top_mem _)
    obtain ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (D.overlapIsPullback i j)
      (g ≫ p) (g ≫ q) (by simpa using congrArg (fun k => g ≫ k) h)
    exact ⟨⟨⟩, φ, h₁.symm, h₂.symm⟩

variable {F : Sheaf (Scheme.zariskiTopology.over S) (Type v)}
  (s : ∀ i : D.J, F.obj.obj (Opposite.op (D.U i)))
  (h : ∀ i j : D.J, F.obj.map (D.f i j).op (s i) =
    F.obj.map ((D.f j i).op ≫ (D.t i j).op) (s j))

/-- Compatible sheaf sections on the relative gluing charts determine
a section on the glued scheme over the base. -/
def sheafValGluedMk : F.obj.obj (Opposite.op D.glued) :=
  Multifork.IsLimit.sectionsEquiv (D.oneHypercover.isLimitMultifork F)
    { val := s, property := fun _ => h _ _ }

/-- The glued section restricts to each prescribed chart section. -/
theorem sheafValGluedMk_val (i : D.J) :
    F.obj.map (D.toGlueData.ι i).op (D.sheafValGluedMk s h) = s i :=
  Multifork.IsLimit.sectionsEquiv_apply_val (D.oneHypercover.isLimitMultifork F) _ _

end RelativeGlueData

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeGluing.Construction.Schemes
