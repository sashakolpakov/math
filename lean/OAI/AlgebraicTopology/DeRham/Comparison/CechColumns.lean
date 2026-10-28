import OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
import OAI.Topology.Euclidean.ProductComplexes

/-! # Cech Columns -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechColumns

noncomputable section

/-!
# Čech columns are actual products of section complexes

A column of the generic Čech double complex is identified with the ordinary
product of the coefficient complexes evaluated on the corresponding open
intersections. The identification is the identity on actual section families
and is natural in the coefficient complex. Consequently, genuine local
quasi-isomorphisms induce quasi-isomorphisms on columns.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.Topology.Euclidean.ProductComplexes.Globalization

universe u

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)
variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ)

/-- The actual section complex on an intersection indexed by a Čech tuple. -/
def cechIntersectionComplex {p : ℕ} (a : Fin (p + 1) → ι) :
    CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  ((((evaluation ((Opens X)ᵒᵖ) (ModuleCat.{u} ℂ)).obj
    (op (SmoothCech.cechIntersection U a))).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

@[simp]
theorem cechIntersectionComplex_X {p : ℕ} (a : Fin (p + 1) → ι) (q : ℕ) :
    (cechIntersectionComplex U K a).X q =
      (K.X q).obj (op (SmoothCech.cechIntersection U a)) := rfl

@[simp]
theorem cechIntersectionComplex_d {p : ℕ} (a : Fin (p + 1) → ι) (q r : ℕ) :
    (cechIntersectionComplex U K a).d q r =
      (K.d q r).app (op (SmoothCech.cechIntersection U a)) := rfl

/-- A Čech column is the product of the actual section complexes of its
intersection domains. The isomorphism is the identity on section families. -/
def cechColumnProductIso (p : ℕ) :
    (CechDoubleComplexFunctor.cechDoubleComplex U K).X p ≅
      Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex ℂ
        (fun a : Fin (p + 1) → ι => cechIntersectionComplex U K a) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro q r _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    rfl)

@[simp]
theorem cechColumnProductIso_hom_f_apply (p q : ℕ)
    (c : SmoothCech.CechCochain (K.X q) U p) :
    ((cechColumnProductIso U K p).hom.f q) c = c := rfl

@[simp]
theorem cechColumnProductIso_inv_f_apply (p q : ℕ)
    (c : SmoothCech.CechCochain (K.X q) U p) :
    ((cechColumnProductIso U K p).inv.f q) c = c := rfl

/-- Exactness of all intersection section complexes gives exactness of the
corresponding Čech column, including in degree zero. -/
theorem cechDoubleComplex_column_exactAt (p q : ℕ)
    (h : ∀ a : Fin (p + 1) → ι, (cechIntersectionComplex U K a).ExactAt q) :
    ((CechDoubleComplexFunctor.cechDoubleComplex U K).X p).ExactAt q := by
  exact (Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex_exactAt ℂ
    (fun a : Fin (p + 1) → ι => cechIntersectionComplex U K a) q h).of_iso
      (cechColumnProductIso U K p).symm

variable {K}
variable {L : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ}

/-- The actual map on an intersection section complex induced by a
coefficient cochain morphism. -/
def cechIntersectionMap (φ : K ⟶ L) {p : ℕ} (a : Fin (p + 1) → ι) :
    cechIntersectionComplex U K a ⟶ cechIntersectionComplex U L a :=
  ((((evaluation ((Opens X)ᵒᵖ) (ModuleCat.{u} ℂ)).obj
    (op (SmoothCech.cechIntersection U a))).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)

@[simp]
theorem cechIntersectionMap_f (φ : K ⟶ L) {p : ℕ}
    (a : Fin (p + 1) → ι) (q : ℕ) :
    (cechIntersectionMap U φ a).f q =
      (φ.f q).app (op (SmoothCech.cechIntersection U a)) := rfl

/-- The column/product identification preserves the actual coefficient map
on every intersection. -/
theorem cechColumnProductIso_naturality (φ : K ⟶ L) (p : ℕ) :
    (CechDoubleComplexFunctor.cechDoubleComplexMap U φ).f p ≫ (cechColumnProductIso U L p).hom =
      (cechColumnProductIso U K p).hom ≫
        Topology.Euclidean.ProductComplexes.Globalization.indexedProductMap ℂ
          (fun a : Fin (p + 1) → ι => cechIntersectionMap U φ a) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  rfl

/-- Actual quasi-isomorphisms on every intersection induce an actual
quasi-isomorphism on the corresponding Čech column. -/
theorem cechDoubleComplexMap_column_quasiIso (φ : K ⟶ L) (p : ℕ)
    (h : ∀ a : Fin (p + 1) → ι, QuasiIso (cechIntersectionMap U φ a)) :
    QuasiIso ((CechDoubleComplexFunctor.cechDoubleComplexMap U φ).f p) := by
  have hprod := Topology.Euclidean.ProductComplexes.Globalization.indexedProductMap_quasiIso ℂ
    (fun a : Fin (p + 1) → ι => cechIntersectionMap U φ a) h
  let e : Arrow.mk ((CechDoubleComplexFunctor.cechDoubleComplexMap U φ).f p) ≅
      Arrow.mk (Topology.Euclidean.ProductComplexes.Globalization.indexedProductMap ℂ
        (fun a : Fin (p + 1) → ι => cechIntersectionMap U φ a)) :=
    Arrow.isoMk (cechColumnProductIso U K p) (cechColumnProductIso U L p)
      (cechColumnProductIso_naturality U φ p).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e).2 hprod

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechColumns
