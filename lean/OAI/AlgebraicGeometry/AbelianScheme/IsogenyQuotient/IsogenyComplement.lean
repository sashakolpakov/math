import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Inclusion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Descent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Epi

/-! # Isogeny Complement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction

noncomputable section

/-!
The relative quotient adapter for IsogenyQuotient. The AbelianScheme bundle from the
proved PoincareBundle infrastructure has precisely FiniteDescent's smooth proper commutative
group-scheme conditions with geometrically connected fibers. FiniteDescentInput below
states the supplied quotient proposition with that concrete bundle; no
statement stub is imported or used as a proved theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

def FiniteLocallyFreeMap {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f

/-- The exact quotient and universal-property content of the FiniteDescent input. -/
def FiniteDescentInput : Prop :=
  ∀ (S : Scheme.{u}) (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S)
    (H : Over S) [GrpObj H] (i : H ⟶ A.toOver) [IsMonHom i]
    (_hi : IsClosedImmersion i.left) (_hH : FiniteLocallyFreeMap H.hom),
    ∃ (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (q : A.toOver ⟶ B.toOver),
      IsMonHom q ∧ FiniteLocallyFreeMap q.left ∧ Surjective q.left ∧
      (∀ (T : Over S) (a : T ⟶ A.toOver),
        a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) ∧
      Descent.Construction.QuotientUniversalProperty i q

/-- The abelian scheme over the parameter space, with the group law
constructed on its actual base change. -/
def baseChangedAbelianScheme
    {S : Scheme.{u}} (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (P : Over S) :
    Picard.PoincareBundle.Epi.Construction.AbelianScheme P.left where
  toOver := (Kernel.Inclusion.Construction.ambientGroupScheme A.toOver P).X
  group := inferInstance
  commutative := inferInstance
  smooth := by
    change Smooth (pullback.fst P.hom A.toOver.hom)
    infer_instance
  proper := by
    change IsProper (pullback.fst P.hom A.toOver.hom)
    infer_instance
  geometricallyConnected := by
    change GeometricallyConnected (pullback.fst P.hom A.toOver.hom)
    infer_instance

/-- Apply FiniteDescent to the constructed relative kernel and its verified closed
group-scheme embedding. The resulting map has the required kernel on all
test schemes and the full invariant-morphism universal property. -/
theorem relative_quotient_of_FiniteDescent
    {S : Scheme.{u}} (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (P : Over S)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.toOver P) (R : F.Model)
    (h_FiniteDescent : FiniteDescentInput.{u}) :
    ∃ (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme P.left)
      (q : (baseChangedAbelianScheme A P).toOver ⟶ B.toOver),
      IsMonHom q ∧ FiniteLocallyFreeMap q.left ∧ Surjective q.left ∧
      (∀ (T : Over P.left) (a : T ⟶ (baseChangedAbelianScheme A P).toOver),
        a ≫ q = 1 ↔
          ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
            h ≫ (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom = a) ∧
      Descent.Construction.QuotientUniversalProperty (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom q := by
  have hmon : IsMonHom (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom :=
    (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.isMonHom_hom
  exact @h_FiniteDescent P.left (baseChangedAbelianScheme A P) (Subgroup.Construction.subgroupGroupScheme F R).X
    (Subgroup.Construction.subgroupGroupScheme F R).grp (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom hmon
    (Kernel.Inclusion.Construction.subgroupInclusion_closedImmersion F R)
    (Subgroup.Construction.subgroupGroupScheme_finiteLocallyFree F R)

/-- An n-torsion relative subgroup yields an actual quotient isogeny
and a complementary homomorphism whose two composites are [n]. -/
theorem quotient_isogeny_and_complement_of_FiniteDescent
    {S : Scheme.{u}} (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (P : Over S)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.toOver P) (R : F.Model)
    (n : ℕ) (hkilled : F.KilledBy n) (h_FiniteDescent : FiniteDescentInput.{u}) :
    ∃ (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme P.left)
      (f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny (baseChangedAbelianScheme A P) B)
      (g : B.toOver ⟶ (baseChangedAbelianScheme A P).toOver),
      IsMonHom g ∧
      f.hom ≫ g = (𝟙 (baseChangedAbelianScheme A P).toOver) ^ n ∧
      g ≫ f.hom = (𝟙 B.toOver) ^ n ∧
      (∀ (T : Over P.left) (a : T ⟶ (baseChangedAbelianScheme A P).toOver),
        a ≫ f.hom = 1 ↔
          ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
            h ≫ (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom = a) ∧
      Descent.Construction.QuotientUniversalProperty (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom f.hom := by
  obtain ⟨B, q, hqMon, hqFinite, hqSurj, hkernel, hUP⟩ :=
    relative_quotient_of_FiniteDescent A P F R h_FiniteDescent
  let i := (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom
  have hiMon : IsMonHom i := (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.isMonHom_hom
  have : IsClosedImmersion i.left := Kernel.Inclusion.Construction.subgroupInclusion_closedImmersion F R
  have : Mono i := Over.mono_of_mono_left i
  have : IsMonHom q := hqMon
  have : IsFinite q.left := hqFinite.1
  have : Flat q.left := hqFinite.2.1
  have : Surjective q.left := hqSurj
  have : LocallyOfFinitePresentation q.left := hqFinite.2.2
  have hiq : i ≫ q = 1 := by
    apply (hkernel (Subgroup.Construction.subgroupGroupScheme F R).X i).mpr
    refine ⟨𝟙 _, Category.id_comp _, ?_⟩
    intro h hh
    apply (cancel_mono i).mp
    simpa only [Category.id_comp] using hh
  have hin : i ^ n = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp,
      Subgroup.Construction.subgroupGroupScheme_killed F R n hkilled, MonObj.one_comp]
  obtain ⟨g, ⟨hqg, hgq⟩, _⟩ := @Descent.Construction.complementary_map_of_FiniteDescent (Over P.left) _ _
    (baseChangedAbelianScheme A P).toOver B.toOver (Subgroup.Construction.subgroupGroupScheme F R).X
    (baseChangedAbelianScheme A P).group B.group _
    (baseChangedAbelianScheme A P).commutative i q hqMon hiq hUP n hin
  have : EffectiveEpi (q ⊗ₘ q) := Picard.PoincareBundle.Epi.Construction.effectiveEpi_tensor_over_of_fpqc q q
  have : IsMonHom ((𝟙 (baseChangedAbelianScheme A P).toOver) ^ n) :=
    Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 _) n
  have hgMon : IsMonHom g := Picard.PoincareBundle.Epi.Construction.isMonHom_of_comp q _ g hqg
  let f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny (baseChangedAbelianScheme A P) B := {
    hom := q
    isMonHom := hqMon
    finite := hqFinite.1
    flat := hqFinite.2.1
    surjective := hqSurj
    finitePresentation := hqFinite.2.2
  }
  exact ⟨B, f, g, hgMon, hqg, hgq, hkernel, hUP⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction
