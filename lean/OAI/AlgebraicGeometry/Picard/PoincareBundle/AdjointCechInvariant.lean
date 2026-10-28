import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Adjoint Cech Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

noncomputable section

/-!
# The invariant equalizer and its geometric gluing comparison
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {L : C ⥤ D} {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D}
  (a : L ⊣ R) (b : P ⊣ U) (c : Q ⊣ V) (e : U ⋙ R ≅ V ⋙ R)

/-- The canonical comparison between the two iterated pullbacks. -/
def pullbackGluing : L ⋙ P ≅ L ⋙ Q :=
  ((a.comp b).ofNatIsoRight e).leftAdjointUniq (a.comp c)

variable {M : D}

/-- The direct-image map obtained by restricting and then applying the gluing. -/
def leftMap (σ : P.obj M ⟶ Q.obj M) : R.obj M ⟶ (V ⋙ R).obj (Q.obj M) :=
  R.map (b.unit.app M) ≫ e.hom.app (P.obj M) ≫ (V ⋙ R).map σ

/-- The other direct-image map restricts to the second projection. -/
def rightMap : R.obj M ⟶ (V ⋙ R).obj (Q.obj M) := R.map (c.unit.app M)

/-- The composite adjunction evaluates a pulled-back morphism by the corresponding unit map. -/
theorem comp_homEquiv_map_comp {N : C} {W : E} (φ : L.obj N ⟶ M) (σ : P.obj M ⟶ W) :
    (a.comp b).homEquiv N W (P.map φ ≫ σ) =
      a.homEquiv N M φ ≫ R.map (b.unit.app M) ≫ (U ⋙ R).map σ := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, b.homEquiv_naturality_left,
    a.homEquiv_naturality_right, b.homEquiv_unit, R.map_comp]
  rfl

theorem left_homEquiv {N : C} (φ : L.obj N ⟶ M) (σ : P.obj M ⟶ Q.obj M) :
    ((a.comp b).ofNatIsoRight e).homEquiv N (Q.obj M) (P.map φ ≫ σ) =
      a.homEquiv N M φ ≫ leftMap b e σ := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, comp_homEquiv_map_comp]
  change (a.homEquiv N M φ ≫ R.map (b.unit.app M) ≫ (U ⋙ R).map σ) ≫
    e.hom.app (Q.obj M) = _
  simp only [Category.assoc]
  rw [e.hom.naturality σ]
  rfl

theorem right_homEquiv {N : C} (φ : L.obj N ⟶ M) :
    ((a.comp b).ofNatIsoRight e).homEquiv N (Q.obj M)
        ((pullbackGluing a b c e).hom.app N ≫ Q.map φ) =
      a.homEquiv N M φ ≫ rightMap (R := R) c := by
  unfold pullbackGluing
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← (a.comp c).homEquiv_unit]
  have h := comp_homEquiv_map_comp a c φ (𝟙 (Q.obj M))
  rw [Category.comp_id, (V ⋙ R).map_id] at h
  erw [Category.comp_id] at h
  exact h

/-- A morphism from the pullback is compatible with gluing exactly when its adjoint equalizes the
two direct-image maps. -/
theorem compatible_iff {N : C} (φ : L.obj N ⟶ M) (σ : P.obj M ⟶ Q.obj M) :
    P.map φ ≫ σ = (pullbackGluing a b c e).hom.app N ≫ Q.map φ ↔
      a.homEquiv N M φ ≫ leftMap b e σ = a.homEquiv N M φ ≫ rightMap (R := R) c := by
  constructor
  · intro h
    have hh := congrArg (((a.comp b).ofNatIsoRight e).homEquiv N (Q.obj M)) h
    rw [left_homEquiv, right_homEquiv] at hh
    exact hh
  · intro h
    apply (((a.comp b).ofNatIsoRight e).homEquiv N (Q.obj M)).injective
    rw [left_homEquiv, right_homEquiv]
    exact h

variable [HasEqualizers C]

/-- The global invariant object defined directly from the gluing is an actual equalizer. -/
def invariants (σ : P.obj M ⟶ Q.obj M) : C := equalizer (leftMap b e σ) (rightMap (R := R) c)

/-- The invariant equalizer has its canonical pullback comparison to the original object. -/
def comparison (σ : P.obj M ⟶ Q.obj M) : L.obj (invariants b c e σ) ⟶ M :=
  (a.homEquiv _ M).symm (equalizer.ι (leftMap b e σ) (rightMap (R := R) c))

/-- This comparison respects the full original gluing morphism. -/
theorem comparison_compatible (σ : P.obj M ⟶ Q.obj M) :
    P.map (comparison a b c e σ) ≫ σ =
      (pullbackGluing a b c e).hom.app (invariants b c e σ) ≫ Q.map (comparison a b c e σ) := by
  apply (compatible_iff a b c e _ σ).mpr
  have hη : a.homEquiv _ M (comparison a b c e σ) =
      equalizer.ι (leftMap b e σ) (rightMap (R := R) c) :=
    (a.homEquiv _ M).apply_symm_apply _
  exact (congrArg (fun k => k ≫ leftMap b e σ) hη).trans
    ((equalizer.condition _ _).trans (congrArg (fun k => k ≫ rightMap (R := R) c) hη.symm))

/-- Morphisms from a pullback that respect the supplied gluing. -/
def CompatibleHom (N : C) (σ : P.obj M ⟶ Q.obj M) :=
  { φ : L.obj N ⟶ M // P.map φ ≫ σ = (pullbackGluing a b c e).hom.app N ≫ Q.map φ }

/-- The invariant equalizer represents all gluing-compatible morphisms from pullbacks. -/
def invariantHomEquiv (N : C) (σ : P.obj M ⟶ Q.obj M) :
    CompatibleHom a b c e N σ ≃ (N ⟶ invariants b c e σ) where
  toFun φ := equalizer.lift (a.homEquiv N M φ.val) ((compatible_iff a b c e φ.val σ).mp φ.property)
  invFun k := ⟨(a.homEquiv N M).symm (k ≫ equalizer.ι _ _), by
    apply (compatible_iff a b c e _ σ).mpr
    have hη := (a.homEquiv N M).apply_symm_apply (k ≫ equalizer.ι (leftMap b e σ) (rightMap (R := R) c))
    have hk : (k ≫ equalizer.ι (leftMap b e σ) (rightMap (R := R) c)) ≫ leftMap b e σ =
        (k ≫ equalizer.ι (leftMap b e σ) (rightMap (R := R) c)) ≫ rightMap (R := R) c := by
      erw [Category.assoc, equalizer.condition, ← Category.assoc]
    exact (congrArg (fun t => t ≫ leftMap b e σ) hη).trans
      (hk.trans (congrArg (fun t => t ≫ rightMap (R := R) c) hη.symm))⟩
  left_inv φ := by
    apply Subtype.ext
    change (a.homEquiv N M).symm
      (equalizer.lift (a.homEquiv N M φ.val) _ ≫ equalizer.ι _ _) = φ.val
    rw [equalizer.lift_ι]
    exact (a.homEquiv N M).symm_apply_apply φ.val
  right_inv k := by
    apply equalizer.hom_ext
    erw [equalizer.lift_ι]
    exact (a.homEquiv N M).apply_symm_apply (k ≫ equalizer.ι _ _)

/-- Adjunction sends the canonical pullback comparison to the invariant inclusion. -/
theorem comparison_homEquiv (σ : P.obj M ⟶ Q.obj M) :
    a.homEquiv _ M (comparison a b c e σ) = equalizer.ι (leftMap b e σ) (rightMap (R := R) c) :=
  (a.homEquiv _ M).apply_symm_apply _

theorem homEquiv_map_comparison {N : C} (σ : P.obj M ⟶ Q.obj M)
    (k : N ⟶ invariants b c e σ) :
    a.homEquiv N M (L.map k ≫ comparison a b c e σ) =
      k ≫ equalizer.ι (leftMap b e σ) (rightMap (R := R) c) :=
  (a.homEquiv_naturality_left k (comparison a b c e σ)).trans
    (congrArg (fun t => k ≫ t) (comparison_homEquiv a b c e σ))

/-- Every gluing-compatible morphism factors uniquely through the actual invariant comparison. -/
theorem existsUnique_lift {N : C} (σ : P.obj M ⟶ Q.obj M)
    (φ : CompatibleHom a b c e N σ) :
    ∃! k : N ⟶ invariants b c e σ, L.map k ≫ comparison a b c e σ = φ.val := by
  let k := (invariantHomEquiv a b c e N σ) φ
  have hk : L.map k ≫ comparison a b c e σ = φ.val := by
    apply (a.homEquiv N M).injective
    rw [homEquiv_map_comparison]
    exact equalizer.lift_ι _ _
  refine ⟨k, hk, ?_⟩
  intro l hl
  apply equalizer.hom_ext
  calc
    _ = a.homEquiv N M (L.map l ≫ comparison a b c e σ) :=
      (homEquiv_map_comparison a b c e σ l).symm
    _ = a.homEquiv N M φ.val := congrArg (a.homEquiv N M) hl
    _ = a.homEquiv N M (L.map k ≫ comparison a b c e σ) :=
      (congrArg (a.homEquiv N M) hk).symm
    _ = _ := homEquiv_map_comparison a b c e σ k

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant
