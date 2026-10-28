import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Subgroup Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction

noncomputable section

/-!
Transport subgroup families along their actual group-scheme inclusions.
The subgroup model is retained, including over nonreduced parameter
schemes. In particular, an TorsionQuotient choice killed by n becomes a subgroup of
the native finite-etale torsion group with no new geometric assumption.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B P : Over S} [GrpObj A] [GrpObj B]

def relativeSubgroupImage (f : B ⟶ A) [IsMonHom f]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points X t := (F.points X t).map (IsMonHom.monoidHom f X)
  naturality := by
    intro X Y a t x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨a ≫ y, F.naturality a t hy, Category.assoc a y f⟩

def relativeSubgroupPullback (f : B ⟶ A) [IsMonHom f]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P where
  points X t := (F.points X t).comap (IsMonHom.monoidHom f X)
  naturality := by
    intro X Y a t x hx
    change (a ≫ x) ≫ f ∈ F.points X (a ≫ t)
    rw [Category.assoc]
    exact F.naturality a t hx

theorem relativeSubgroupImage_baseChange
    (f : B ⟶ A) [IsMonHom f] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P)
    {Q : Over S} (b : Q ⟶ P) :
    (relativeSubgroupImage f F).baseChange b = relativeSubgroupImage f (F.baseChange b) := rfl

theorem relativeSubgroupPullback_baseChange
    (f : B ⟶ A) [IsMonHom f] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    {Q : Over S} (b : Q ⟶ P) :
    (relativeSubgroupPullback f F).baseChange b = relativeSubgroupPullback f (F.baseChange b) := rfl

/-- A monomorphic group-scheme embedding transports the represented
subgroup with exactly the same finite locally free parameter scheme. -/
def relativeSubgroupImage_model
    (f : B ⟶ A) [IsMonHom f] [Mono f]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) (R : F.Model) :
    (relativeSubgroupImage f F).Model where
  carrier := R.carrier
  toBase := R.toBase
  toGroup := R.toGroup ≫ f
  finite := R.finite
  flat := R.flat
  finitePresentation := R.finitePresentation
  jointly_monic X a b hbase hgroup :=
    R.jointly_monic X a b hbase ((cancel_mono f).mp (by
      simpa only [Category.assoc] using hgroup))
  points_iff X t a := by
    constructor
    · rintro ⟨x, hx, hxa⟩
      obtain ⟨r, hrt, hrx⟩ := (R.points_iff X t x).mp hx
      exact ⟨r, hrt, by rw [← Category.assoc, hrx]; exact hxa⟩
    · rintro ⟨r, hrt, hra⟩
      exact ⟨r ≫ R.toGroup,
        (R.points_iff X t _).mpr ⟨r, hrt, rfl⟩,
        by
          change (r ≫ R.toGroup) ≫ f = a
          exact (Category.assoc _ _ _).trans hra⟩

/-- A verified factor of the universal subgroup embedding gives a
geometric model for its pullback along a monomorphism. -/
def relativeSubgroupPullback_model
    (f : B ⟶ A) [IsMonHom f] [Mono f]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (l : R.carrier ⟶ B) (hl : l ≫ f = R.toGroup) :
    (relativeSubgroupPullback f F).Model where
  carrier := R.carrier
  toBase := R.toBase
  toGroup := l
  finite := R.finite
  flat := R.flat
  finitePresentation := R.finitePresentation
  jointly_monic X a b hbase hgroup := by
    apply R.jointly_monic X a b hbase
    rw [← hl, ← Category.assoc, ← Category.assoc, hgroup]
  points_iff X t a := by
    change a ≫ f ∈ F.points X t ↔ ∃ r, r ≫ R.toBase = t ∧ r ≫ l = a
    rw [R.points_iff]
    constructor
    · rintro ⟨r, hrt, hra⟩
      refine ⟨r, hrt, (cancel_mono f).mp ?_⟩
      rw [Category.assoc, hl, hra]
    · rintro ⟨r, hrt, hra⟩
      exact ⟨r, hrt, by rw [← hl, ← Category.assoc, hra]⟩

theorem relativeSubgroupPullback_image
    (f : B ⟶ A) [IsMonHom f]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (hfactor : ∀ (X : Over S) (t : X ⟶ P) (x : X ⟶ A),
      x ∈ F.points X t → ∃ y : X ⟶ B, y ≫ f = x) :
    relativeSubgroupImage f (relativeSubgroupPullback f F) = F := by
  ext X t x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, hy⟩ := hfactor X t x hx
    exact ⟨y, by change y ≫ f ∈ F.points X t; rw [hy]; exact hx, hy⟩

variable [IsCommMonObj A]

/-- An TorsionQuotient subgroup choice killed by n has a model inside the actual
finite-etale n-torsion group, retaining its original underlying scheme. -/
def torsionRelativeSubgroup_model
    (n : ℕ) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) (hkilled : F.KilledBy n) :
    (relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) F).Model :=
  relativeSubgroupPullback_model (Torsion.Groups.Construction.nativeTorsionInclusion A n) F R
    (Torsion.Groups.Construction.nativeTorsionLift A n R.toGroup (R.toGroup_pow_eq_one hkilled))
    (Torsion.Groups.Construction.nativeTorsionLift_inclusion A n R.toGroup (R.toGroup_pow_eq_one hkilled))

/-- Returning the lifted torsion subgroup to the abelian scheme recovers
the original family exactly. -/
theorem torsionRelativeSubgroup_image
    (n : ℕ) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hkilled : F.KilledBy n) :
    relativeSubgroupImage (Torsion.Groups.Construction.nativeTorsionInclusion A n)
      (relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) F) = F := by
  apply relativeSubgroupPullback_image
  intro X t x hx
  exact ⟨Torsion.Groups.Construction.nativeTorsionLift A n x (hkilled X t x hx), Torsion.Groups.Construction.nativeTorsionLift_inclusion _ _ _ _⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction
