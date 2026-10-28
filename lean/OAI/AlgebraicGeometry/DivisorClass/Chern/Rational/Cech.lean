import OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor
import OAI.AlgebraicTopology.Cohomology.Singular.CechComparison

/-! # Cech -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech

noncomputable section

/-!
# ChernClass: rational Cech complexes

These are rational-coefficient versions of the existing section, coefficient,
and total-complex constructions. The formulas and proofs are unchanged except
for coefficients and namespace. Actual open restrictions are used throughout.
No new comparison assumptions or computational-limit overrides are introduced.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor OAI.AlgebraicTopology.Cohomology.Singular.CechComparison
open scoped Simplicial BigOperators

universe u

section

variable {X ι : Type u} [TopologicalSpace X]
variable (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) (U : ι → Opens X)

/-- Actual sections of a presheaf on all intersections of n+1 cover members. -/
abbrev CechCochain (n : ℕ) :=
  (a : Fin (n + 1) → ι) → F.obj (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))

/-- Restriction along a tuple-index map, applied to genuine sections. -/
def cechPrecomp {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) :
    CechCochain F U n →ₗ[ℚ] CechCochain F U m where
  toFun c a := (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f)).op).hom
    (c (a ∘ f))
  map_add' c d := by
    funext a
    exact map_add _ _ _
  map_smul' z c := by
    funext a
    exact map_smul _ _ _

/-- The Čech cosimplicial module of the given presheaf and open family. -/
def cechCosimplicial : CosimplicialObject (ModuleCat.{u} ℚ) where
  obj n := ModuleCat.of ℚ (CechCochain F U n.len)
  map f := ModuleCat.ofHom (cechPrecomp F U f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a id)).op).hom (c a) = c a
    rw [show (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a id)).op =
      𝟙 (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) from Subsingleton.elim _ _]
    exact congrArg (fun k => k.hom (c a)) (F.map_id (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)))
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a
      (g.toOrderHom ∘ f.toOrderHom))).op).hom (c (a ∘ g.toOrderHom ∘ f.toOrderHom)) =
      (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a g.toOrderHom)).op).hom
        ((F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U (a ∘ g.toOrderHom)
          f.toOrderHom)).op).hom (c (a ∘ g.toOrderHom ∘ f.toOrderHom)))
    rw [show (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a
      (g.toOrderHom ∘ f.toOrderHom))).op =
        (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U (a ∘ g.toOrderHom) f.toOrderHom)).op ≫
        (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a g.toOrderHom)).op
      from Subsingleton.elim _ _, F.map_comp]
    rfl

/-- The actual Čech cochain complex, with the alternating restriction differential. -/
def cechComplex : CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (cechCosimplicial F U)

/-- The signed Čech differential as a linear map on the explicit section families. -/
def cechDelta (n : ℕ) : CechCochain F U n →ₗ[ℚ] CechCochain F U (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial F U) n).hom

/-- The differential is the usual alternating sum of restrictions with one
index omitted at a time. -/
theorem cechDelta_apply (n : ℕ) (c : CechCochain F U n)
    (a : Fin (n + 2) → ι) :
    cechDelta F U n c a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)).op).hom
          (c (a ∘ j.succAbove)) := by
  classical
  simp only [cechDelta, AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  change ((∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    cechPrecomp F U j.succAbove) c) a = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  rfl

theorem cechDelta_squared (n : ℕ) (c : CechCochain F U n) :
    cechDelta F U (n + 1) (cechDelta F U n c) = 0 := by
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (cechCosimplicial F U) n
  exact congrArg (fun f => f.hom c) h

/-- The bundled cochain differential is exactly the explicit signed map. -/
theorem cechComplex_d (n : ℕ) :
    (cechComplex F U).d n (n + 1) = ModuleCat.ofHom (cechDelta F U n) := by
  exact CochainComplex.of_d
    (fun k => (cechCosimplicial F U).obj ⦋k⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial F U)) n

variable {κ : Type u} (V : κ → Opens X) (r : κ → ι)
  (hr : ∀ k, V k ≤ U (r k))

include hr in
/-- A refinement of open families gives inclusions on every finite intersection. -/
theorem cechIntersection_refinement_le {n : ℕ} (a : Fin (n + 1) → κ) :
    OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a ≤ OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a) :=
  le_iInf (fun k => (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a k).trans (hr (a k)))

/-- The actual section restriction associated to a refinement of the open family. -/
def cechRefinementMap (n : ℕ) : CechCochain F U n →ₗ[ℚ] CechCochain F V n where
  toFun c a := (F.map (homOfLE (cechIntersection_refinement_le U V r hr a)).op).hom
    (c (r ∘ a))
  map_add' c d := by
    funext a
    exact map_add _ _ _
  map_smul' z c := by
    funext a
    exact map_smul _ _ _

omit U V r hr in
/-- Functoriality of actual presheaf restrictions, in the section notation. -/
theorem cechSection_restrict_trans {A B C : Opens X} (hBA : B ≤ A) (hCB : C ≤ B)
    (s : F.obj (op A)) :
    (F.map (homOfLE hCB).op).hom ((F.map (homOfLE hBA).op).hom s) =
      (F.map (homOfLE (hCB.trans hBA)).op).hom s := by
  exact (congrArg (fun k => k.hom s) (F.map_comp (homOfLE hBA).op (homOfLE hCB).op)).symm

/-- Refinement restriction is natural for all cosimplicial operators. -/
def cechRefinementNat : cechCosimplicial F U ⟶ cechCosimplicial F V where
  app n := ModuleCat.ofHom (cechRefinementMap F U V r hr n.len)
  naturality n m f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (F.map (homOfLE (cechIntersection_refinement_le U V r hr a)).op).hom
        ((F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U (r ∘ a) f.toOrderHom)).op).hom
          (c (r ∘ a ∘ f.toOrderHom))) =
      (F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp V a f.toOrderHom)).op).hom
        ((F.map (homOfLE (cechIntersection_refinement_le U V r hr
          (a ∘ f.toOrderHom))).op).hom (c (r ∘ a ∘ f.toOrderHom)))
    rw [cechSection_restrict_trans, cechSection_restrict_trans]

/-- The induced map of actual Čech complexes under a cover refinement. -/
def cechRefinement : cechComplex F U ⟶ cechComplex F V :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (cechRefinementNat F U V r hr)

@[simp]
theorem cechRefinement_f (n : ℕ) :
    (cechRefinement F U V r hr).f n = ModuleCat.ofHom (cechRefinementMap F U V r hr n) := rfl

/-- Refinement commutes with the signed differential on the nose. -/
theorem cechRefinementMap_delta (n : ℕ) (c : CechCochain F U n) :
    cechRefinementMap F U V r hr (n + 1) (cechDelta F U n c) =
      cechDelta F V n (cechRefinementMap F U V r hr n c) := by
  have h := (cechRefinement F U V r hr).comm n (n + 1)
  rw [cechComplex_d, cechComplex_d, cechRefinement_f, cechRefinement_f] at h
  exact (congrArg (fun k => k.hom c) h).symm

end

section

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)
variable {F G : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ} (α : F ⟶ G)

/-- A morphism of actual presheaves acts on each Čech section. -/
def cechCoefficientMap (n : ℕ) :
    CechCochain F U n →ₗ[ℚ] CechCochain G U n where
  toFun c a := (α.app (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom (c a)
  map_add' c d := by
    funext a
    exact map_add _ _ _
  map_smul' z c := by
    funext a
    exact map_smul _ _ _

/-- Coefficient maps are natural for every Čech cosimplicial operator. -/
def cechCoefficientNat : cechCosimplicial F U ⟶ cechCosimplicial G U where
  app n := ModuleCat.ofHom (cechCoefficientMap U α n.len)
  naturality n m f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (α.app (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
      ((F.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op).hom
        (c (a ∘ f.toOrderHom))) =
      (G.map (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op).hom
        ((α.app (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ f.toOrderHom)))).hom
          (c (a ∘ f.toOrderHom)))
    exact congrArg (fun k => k.hom (c (a ∘ f.toOrderHom)))
      (α.naturality (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op)

/-- A presheaf morphism induces the ordinary coefficient map of Čech complexes. -/
def cechCoefficientHom : cechComplex F U ⟶ cechComplex G U :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (cechCoefficientNat U α)

@[simp]
theorem cechCoefficientHom_f (n : ℕ) :
    (cechCoefficientHom U α).f n = ModuleCat.ofHom (cechCoefficientMap U α n) := rfl

/-- Acting on coefficients commutes with the signed Čech differential. -/
theorem cechCoefficientMap_delta (n : ℕ) (c : CechCochain F U n) :
    cechCoefficientMap U α (n + 1) (cechDelta F U n c) =
      cechDelta G U n (cechCoefficientMap U α n c) := by
  have h := (cechCoefficientHom U α).comm n (n + 1)
  rw [cechComplex_d, cechComplex_d, cechCoefficientHom_f, cechCoefficientHom_f] at h
  exact (congrArg (fun k => k.hom c) h).symm

end

section

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)

/-- A genuine coefficient presheaf is sent to its actual Čech complex. -/
def cechComplexFunctor :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℕ where
  obj F := cechComplex F U
  map α := cechCoefficientHom U α
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
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ ⥤
      HomologicalComplex₂ (ModuleCat.{u} ℚ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{u} ℚ)
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)

/-- The double complex of actual sections of a coefficient complex. -/
abbrev cechDoubleComplex
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ) :=
  (cechDoubleComplexFunctor U).obj K

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ)

/-- Bidegree `(p,q)` consists of actual `K^q` sections on all ordered
`(p+1)`-fold intersections. -/
@[simp]
theorem cechDoubleComplex_XX (p q : ℕ) :
    ((cechDoubleComplex U K).X p).X q =
      ModuleCat.of ℚ (CechCochain (K.X q) U p) := rfl

/-- The horizontal differential is exactly the signed Čech restriction map. -/
@[simp]
theorem cechDoubleComplex_d_f (p q : ℕ) :
    ((cechDoubleComplex U K).d p (p + 1)).f q =
      ModuleCat.ofHom (cechDelta (K.X q) U p) :=
  cechComplex_d (K.X q) U p

/-- The vertical differential applies the actual coefficient differential on
each open intersection. -/
@[simp]
theorem cechDoubleComplex_X_d (p q : ℕ) :
    ((cechDoubleComplex U K).X p).d q (q + 1) =
      ModuleCat.ofHom (cechCoefficientMap U (K.d q (q + 1)) p) := rfl

/-- The two concrete differentials commute, by naturality of the coefficient
differential under actual open restriction. -/
theorem cechDoubleComplex_differentials_commute (p q : ℕ)
    (c : CechCochain (K.X q) U p) :
    cechCoefficientMap U (K.d q (q + 1)) (p + 1) (cechDelta (K.X q) U p c) =
      cechDelta (K.X (q + 1)) U p (cechCoefficientMap U (K.d q (q + 1)) p c) :=
  cechCoefficientMap_delta U (K.d q (q + 1)) p c

/-- Each horizontal row recovers the actual Čech complex of that coefficient
presheaf. -/
@[simp]
theorem cechDoubleComplex_row (q : ℕ) :
    (cechDoubleComplex U K).flip.X q = cechComplex (K.X q) U := rfl

variable {K}
variable {L N : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ}

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
      ModuleCat.ofHom (cechCoefficientMap U (φ.f q) p) := rfl

@[simp]
theorem cechDoubleComplexMap_apply (φ : K ⟶ L) (p q : ℕ)
    (c : CechCochain (K.X q) U p) (a : Fin (p + 1) → ι) :
    (((cechDoubleComplexMap U φ).f p).f q c) a =
      ((φ.f q).app (op (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) (c a) := rfl

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

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)

/-- Actual presheaf complexes map functorially to their signed Čech total complexes. -/
def cechTotalFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ ⥤
      CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  cechDoubleComplexFunctor U ⋙ HomologicalComplex₂.totalFunctor
    (ModuleCat.{u} ℚ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)

/-- The signed total complex of actual Čech sections of a presheaf complex. -/
abbrev cechTotalComplex (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ) :=
  (cechTotalFunctor U).obj K

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ)

/-- Inclusion of an actual section-family summand in the total complex. -/
def cechTotalInclusion (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of ℚ (CechCochain (K.X q) U p) ⟶ (cechTotalComplex U K).X n :=
  (cechDoubleComplex U K).ιTotal (ComplexShape.up ℕ) p q n h

/-- The total differential is the signed sum of the two actual differentials. -/
theorem cechTotalInclusion_d (p q n : ℕ) (h : p + q = n) :
    cechTotalInclusion U K p q n h ≫ (cechTotalComplex U K).d n (n + 1) =
      ModuleCat.ofHom (cechDelta (K.X q) U p) ≫
          cechTotalInclusion U K (p + 1) q (n + 1) (by omega) +
        ((-1 : ℤ) ^ p) • (ModuleCat.ofHom (cechCoefficientMap U (K.d q (q + 1)) p) ≫
          cechTotalInclusion U K p (q + 1) (n + 1) (by omega)) := by
  have hd := OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex.iota_d_of_eq (cechDoubleComplex U K) p q n h
  rw [cechDoubleComplex_d_f, cechDoubleComplex_X_d] at hd
  exact hd

variable {K}
variable {L N : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℚ) ℕ}

/-- A genuine coefficient cochain map induces the actual map on Čech total complexes. -/
abbrev cechTotalMap (φ : K ⟶ L) : cechTotalComplex U K ⟶ cechTotalComplex U L :=
  (cechTotalFunctor U).map φ

/-- The total map is the supplied coefficient map on every actual section summand. -/
theorem cechTotalInclusion_map (φ : K ⟶ L) (p q n : ℕ) (h : p + q = n) :
    cechTotalInclusion U K p q n h ≫ (cechTotalMap U φ).f n =
      ModuleCat.ofHom (cechCoefficientMap U (φ.f q) p) ≫ cechTotalInclusion U L p q n h :=
  HomologicalComplex₂.ιTotal_map (K := cechDoubleComplex U K)
    (L := cechDoubleComplex U L) (φ := cechDoubleComplexMap U φ)
    (c₁₂ := ComplexShape.up ℕ) p q n h

@[simp]
theorem cechTotalMap_id : cechTotalMap U (𝟙 K) = 𝟙 (cechTotalComplex U K) :=
  (cechTotalFunctor U).map_id K

@[simp]
theorem cechTotalMap_comp (φ : K ⟶ L) (ψ : L ⟶ N) :
    cechTotalMap U (φ ≫ ψ) = cechTotalMap U φ ≫ cechTotalMap U ψ :=
  (cechTotalFunctor U).map_comp φ ψ

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech
