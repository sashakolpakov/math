import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELAction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalLifting

/-! # Lie Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRank.Construction

noncomputable section

/-!
Preservation of the actual dual-number Lie eigenspaces in ReferenceFamily. The
infinitesimal point bijection follows from the proved finite-etale lifting
criterion. Addition, scalars, and the integral action are checked on the
scheme maps, so preservation of the prescribed ranks is a conclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {k : Type u} [Field k]

theorem dualNumberReduction_surjective : Function.Surjective (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k) :=
  fun c => ⟨algebraMap k (DualNumber k) c, rfl⟩

theorem dualNumberReduction_ker_nilpotent :
    IsNilpotent (RingHom.ker (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) := by
  let I := RingHom.ker (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)
  have hI : I * I = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    change a * b = 0
    ext <;> simp [ha, hb]
  exact ⟨2, (pow_two I).trans hI⟩

theorem dualNumberOrigin_scalar (c : k) :
    AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c = AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c x).fst = x.fst
  simp only [AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.fst_map]

variable {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f] [IsFinite f.left] [Etale f.left]

omit [IsMonHom f] in
/-- A finite etale homomorphism is injective on actual tangent points. -/
theorem tangent_points_injective
    (x y : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme)
    (hx : AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ x = 1) (hy : AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ y = 1)
    (hxy : x ≫ f = y ≫ f) : x = y := by
  apply Over.OverMorphism.ext
  exact InfinitesimalLifting.Construction.finite_etale_nilpotent_hom_ext f.left (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)
    dualNumberReduction_ker_nilpotent x.left y.left
    (congrArg (fun z => z.left) hxy)
    (congrArg (fun z => z.left) (hx.trans hy.symm))

set_option backward.isDefEq.respectTransparency false in
/-- Every tangent point lifts uniquely from the identity fiber. -/
theorem tangent_points_surjective
    (y : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ B.scheme) (hy : AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ y = 1) :
    ∃ x : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme,
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ x = 1 ∧ x ≫ f = y := by
  let o : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme := 1
  have horigin : o.left ≫ f.left = Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) ≫ y.left := by
    exact congrArg (fun z => z.left) ((MonObj.one_comp f).trans hy.symm)
  obtain ⟨x, hxf, hx₀⟩ := InfinitesimalLifting.Construction.finite_etale_nilpotent_lift f.left (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)
    dualNumberReduction_surjective dualNumberReduction_ker_nilpotent y.left o.left horigin
  have hxbase : x ≫ A.scheme.hom = (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k).hom := by
    rw [← f.w, ← Category.assoc, hxf]
    exact y.w
  let a : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme := Over.homMk x hxbase
  exact ⟨a, Over.OverMorphism.ext hx₀, Over.OverMorphism.ext hxf⟩

variable {R : Type v} [CommRing R]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B) (τ : R →+* k)
variable (hcomm : ∀ r, f ≫ σ.map r = ρ.map r ≫ f)

def lieEigenpointMap : AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ → AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints B σ τ := fun x =>
  ⟨x.val ≫ f, by
    constructor
    · rw [← Category.assoc, x.property.1, MonObj.one_comp]
    · intro r
      rw [Category.assoc, hcomm r, ← Category.assoc, x.property.2 r, Category.assoc]⟩

/-- The etale isogeny gives a bijection of every simultaneous embedding
eigenspace. The inverse's action compatibility follows by uniqueness. -/
theorem lieEigenpointMap_bijective :
    Function.Bijective (lieEigenpointMap A B f ρ σ τ hcomm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact tangent_points_injective A B f x.val y.val x.property.1 y.property.1
      (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx₀, hxf⟩ := tangent_points_surjective A B f y.val y.property.1
    have hxeigen (r : R) : x ≫ ρ.map r = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (τ r) ≫ x := by
      apply tangent_points_injective A B f
      · rw [← Category.assoc, hx₀, MonObj.one_comp]
      · rw [← Category.assoc, dualNumberOrigin_scalar, hx₀]
      · rw [Category.assoc, ← hcomm r, ← Category.assoc, hxf,
          Category.assoc, hxf, y.property.2 r]
    exact ⟨⟨x, hx₀, hxeigen⟩, Subtype.ext hxf⟩

include f hcomm in
/-- The actual ReferenceFamily Lie-rank condition is preserved by the constructed
finite etale equivariant isogeny. -/
theorem hasLieRank_of_finite_etale
    (r : ℕ) (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r) : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B σ τ r := by
  obtain ⟨e, hadd, hscalar⟩ := hr
  let j := Equiv.ofBijective (lieEigenpointMap A B f ρ σ τ hcomm)
    (lieEigenpointMap_bijective A B f ρ σ τ hcomm)
  refine ⟨e.trans j, ?_, ?_⟩
  · intro x y
    change (e (x + y)).val ≫ f = ((e x).val ≫ f) * ((e y).val ≫ f)
    rw [hadd, MonObj.mul_comp]
  · intro c x
    change (e (c • x)).val ≫ f = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c ≫ ((e x).val ≫ f)
    rw [hscalar, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The same rank statement on every geometric fiber is obtained by
genuine scheme base change; the action compatibility is pulled back too. -/
theorem hasLieRank_after_baseChange
    {S : Scheme.{u}} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] [IsFinite f.left] [Etale f.left]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
    (hcomm : ∀ r, f ≫ σ.map r = ρ.map r ≫ f)
    (p : Spec (.of k) ⟶ S) (τ : R →+* k) (r : ℕ)
    (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback p) (ρ.pullback p) τ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (B.pullback p) (σ.pullback p) τ r := by
  let fp : (A.pullback p).scheme ⟶ (B.pullback p).scheme := (Over.pullback p).map f
  have : IsMonHom fp := by
    dsimp only [fp, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
    infer_instance
  have : IsFinite fp.left := MorphismProperty.overPullbackMap p f inferInstance
  have : Etale fp.left := MorphismProperty.overPullbackMap p f inferInstance
  apply hasLieRank_of_finite_etale (A.pullback p) (B.pullback p) fp
    (ρ.pullback p) (σ.pullback p) τ _ r hr
  intro a
  change (Over.pullback p).map f ≫ (Over.pullback p).map (σ.map a) =
    (Over.pullback p).map (ρ.map a) ≫ (Over.pullback p).map f
  simpa only [← Functor.map_comp] using congrArg (Over.pullback p).map (hcomm a)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRank.Construction
