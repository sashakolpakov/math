import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex
import Mathlib.Algebra.Homology.Additive

/-! # Cech Double Complex Functor -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor

noncomputable section

/-!
# The Čech double-complex functor on actual presheaf complexes

The coefficient functor takes a genuine presheaf of complex modules to its
Čech complex on an open family. Applying this functor to a cochain complex
of presheaves and exchanging the two indices produces the actual double
complex with Čech degree first and coefficient degree second.

The construction preserves the actual coefficient maps. Every component is
a product of sections on ordered finite intersections; no acyclicity,
comparison map or geometric identification is assumed.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)

/-- A genuine coefficient presheaf is sent to its actual Čech complex. -/
def cechComplexFunctor :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ⥤ CochainComplex (ModuleCat.{u} ℂ) ℕ where
  obj F := SmoothCech.cechComplex F U
  map α := SmoothCechDoubleComplex.cechCoefficientHom U α
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    rfl
  map_comp α β := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    rfl

/-- The Čech coefficient functor acts additively on actual section maps. -/
instance cechComplexFunctor_additive : (cechComplexFunctor U).Additive where
  map_add := by
    intro _ _ α β
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    rfl

/-- The actual Čech double-complex construction as a functor. The first
index is Čech degree; the second is coefficient degree. -/
def cechDoubleComplexFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ ⥤
      HomologicalComplex₂ (ModuleCat.{u} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{u} ℂ)
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)

/-- The double complex of actual sections of a coefficient complex. -/
abbrev cechDoubleComplex
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ) :=
  (cechDoubleComplexFunctor U).obj K

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ)

/-- Bidegree `(p,q)` consists of actual `K^q` sections on all ordered
`(p+1)`-fold intersections. -/
@[simp]
theorem cechDoubleComplex_XX (p q : ℕ) :
    ((cechDoubleComplex U K).X p).X q =
      ModuleCat.of ℂ (SmoothCech.CechCochain (K.X q) U p) := rfl

/-- The horizontal differential is exactly the signed Čech restriction map. -/
@[simp]
theorem cechDoubleComplex_d_f (p q : ℕ) :
    ((cechDoubleComplex U K).d p (p + 1)).f q =
      ModuleCat.ofHom (SmoothCech.cechDelta (K.X q) U p) :=
  SmoothCech.cechComplex_d (K.X q) U p

/-- The vertical differential applies the actual coefficient differential on
each open intersection. -/
@[simp]
theorem cechDoubleComplex_X_d (p q : ℕ) :
    ((cechDoubleComplex U K).X p).d q (q + 1) =
      ModuleCat.ofHom (SmoothCechDoubleComplex.cechCoefficientMap U (K.d q (q + 1)) p) := rfl

/-- The two concrete differentials commute, by naturality of the coefficient
differential under actual open restriction. -/
theorem cechDoubleComplex_differentials_commute (p q : ℕ)
    (c : SmoothCech.CechCochain (K.X q) U p) :
    SmoothCechDoubleComplex.cechCoefficientMap U (K.d q (q + 1)) (p + 1) (SmoothCech.cechDelta (K.X q) U p c) =
      SmoothCech.cechDelta (K.X (q + 1)) U p (SmoothCechDoubleComplex.cechCoefficientMap U (K.d q (q + 1)) p c) :=
  SmoothCechDoubleComplex.cechCoefficientMap_delta U (K.d q (q + 1)) p c

/-- Each horizontal row recovers the actual Čech complex of that coefficient
presheaf. -/
@[simp]
theorem cechDoubleComplex_row (q : ℕ) :
    (cechDoubleComplex U K).flip.X q = SmoothCech.cechComplex (K.X q) U := rfl

variable {K}
variable {L N : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ}

/-- A genuine morphism of coefficient complexes induces a morphism of the
actual Čech double complexes. -/
abbrev cechDoubleComplexMap (φ : K ⟶ L) :
    cechDoubleComplex U K ⟶ cechDoubleComplex U L :=
  (cechDoubleComplexFunctor U).map φ

/-- The induced comparison acts by the given coefficient map on each
intersection, in each degree. -/
@[simp]
theorem cechDoubleComplexMap_f_f (φ : K ⟶ L) (p q : ℕ) :
    ((cechDoubleComplexMap U φ).f p).f q =
      ModuleCat.ofHom (SmoothCechDoubleComplex.cechCoefficientMap U (φ.f q) p) := rfl

@[simp]
theorem cechDoubleComplexMap_apply (φ : K ⟶ L) (p q : ℕ)
    (c : SmoothCech.CechCochain (K.X q) U p) (a : Fin (p + 1) → ι) :
    (((cechDoubleComplexMap U φ).f p).f q c) a =
      ((φ.f q).app (op (SmoothCech.cechIntersection U a))) (c a) := rfl

@[simp]
theorem cechDoubleComplexMap_id :
    cechDoubleComplexMap U (𝟙 K) = 𝟙 (cechDoubleComplex U K) :=
  (cechDoubleComplexFunctor U).map_id K

@[simp]
theorem cechDoubleComplexMap_comp (φ : K ⟶ L) (ψ : L ⟶ N) :
    cechDoubleComplexMap U (φ ≫ ψ) =
      cechDoubleComplexMap U φ ≫ cechDoubleComplexMap U ψ :=
  (cechDoubleComplexFunctor U).map_comp φ ψ

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
