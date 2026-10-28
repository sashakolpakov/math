import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Epi

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Polarization.Construction

/-!
The relative homomorphism in polarization descent is constructed from the
field-level PoincareBundle input. The candidate is g^vee * lambda * g for a complementary
isogeny g. PoincareBundle makes this candidate n times a polarization on every geometric
fiber. Its restriction to B[n] therefore vanishes on geometric points; TorsionQuotient's
etaleness promotes that equality to a scheme equality. Fpqc descent along
[n] then divides the candidate by n as an actual group-scheme homomorphism.

The input h_PoincareBundle is only the induced homomorphism on geometric point groups
and its pullback identity. It does not assume any relative homomorphism.
The fpqc hypotheses on multiplication maps are displayed explicitly; the
abelian-scheme application still has to furnish those standard properties.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

/-- Divisibility of the source point group replaces injectivity of the
dual isogeny when cancelling a polarized pullback. -/
theorem pullback_point_maps_injective
    {X Y Z W : Type*} [Group X] [Group Y] [Group Z] [Group W]
    (f : X →* Y) (fd : W →* Z) (gd : Z →* W) (n : ℕ)
    (hf : Function.Surjective f)
    (hn : Function.Surjective (fun y : Y => y ^ n))
    (hdual : ∀ w, gd (fd w) = w ^ n)
    (p r : Y →* W) (h : ∀ x, fd (p (f x)) = fd (r (f x))) : p = r := by
  ext y
  obtain ⟨z, hz⟩ := hn y
  change z ^ n = y at hz
  obtain ⟨x, hx⟩ := hf z
  have h' := congrArg gd (h x)
  rw [hdual, hdual, hx, ← p.map_pow, ← r.map_pow, hz] at h'
  exact h'

section Algebra

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B AD BD : C} [GrpObj A] [GrpObj B] [GrpObj AD] [GrpObj BD]

/-- The fieldwise pullback identity identifies the integral candidate
with n times the descended polarization on points. -/
theorem candidate_is_multiple_on_points
    (n : ℕ) (f : A ⟶ B) (g : B ⟶ A)
    (fd : BD ⟶ AD) (gd : AD ⟶ BD)
    (polarization : A ⟶ AD) [IsMonHom polarization]
    (hfg : f ≫ g = (𝟙 A : A ⟶ A) ^ n)
    (hfdgd : fd ≫ gd = (𝟙 BD : BD ⟶ BD) ^ n)
    (T : C) (hf : Function.Surjective (fun a : T ⟶ A => a ≫ f))
    (p : (T ⟶ B) →* (T ⟶ BD))
    (h_PoincareBundle : ∀ a : T ⟶ A, p (a ≫ f) ≫ fd = (a ≫ polarization) ^ n)
    (b : T ⟶ B) : b ≫ g ≫ polarization ≫ gd = p b ^ n := by
  obtain ⟨a, rfl⟩ := hf b
  calc
    (a ≫ f) ≫ g ≫ polarization ≫ gd =
        ((a ^ n) ≫ polarization) ≫ gd := by
          rw [Category.assoc, ← Category.assoc f g, hfg]
          simp only [← Category.assoc, MonObj.comp_pow, Category.comp_id]
    _ = ((a ≫ polarization) ^ n) ≫ gd := by rw [MonObj.pow_comp]
    _ = (p (a ≫ f) ≫ fd) ≫ gd := by rw [h_PoincareBundle]
    _ = p (a ≫ f) ^ n := by
      rw [Category.assoc, hfdgd, MonObj.comp_pow, Category.comp_id]

omit [GrpObj A] [GrpObj AD] in
/-- Pullback of homomorphisms along an isogeny is injective. Complementary
dual maps reduce right cancellation to epimorphic multiplication on B. -/
theorem polarization_pullback_injective
    (n : ℕ) (f : A ⟶ B) [Epi f]
    (fd : BD ⟶ AD) (gd : AD ⟶ BD)
    (hfdgd : fd ≫ gd = (𝟙 BD : BD ⟶ BD) ^ n)
    [Epi ((𝟙 B : B ⟶ B) ^ n)]
    (p r : B ⟶ BD) [IsMonHom p] [IsMonHom r]
    (h : f ≫ p ≫ fd = f ≫ r ≫ fd) : p = r := by
  have h₁ : p ≫ fd = r ≫ fd := (cancel_epi f).mp h
  have h₂ := congrArg (fun t => t ≫ gd) h₁
  simp only [Category.assoc, hfdgd, MonObj.comp_pow, Category.comp_id] at h₂
  apply (cancel_epi ((𝟙 B : B ⟶ B) ^ n)).mp
  simpa only [MonObj.pow_comp, Category.id_comp] using h₂

end Algebra

section Relative

variable {S : Scheme.{u}} {A B AD BD : Over S}
  [GrpObj A] [GrpObj B] [GrpObj AD] [GrpObj BD]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj AD] [IsCommMonObj BD]

omit [IsCommMonObj A] [IsCommMonObj AD] in
/-- The integral candidate kills B[n] as a relative scheme morphism,
using only the geometric-point consequence of PoincareBundle and TorsionQuotient on dual torsion. -/
theorem candidate_kills_torsion_of_TorsionQuotient_PoincareBundle
    (n : ℕ) (f : A ⟶ B) [IsMonHom f]
    [Surjective f.left] [LocallyOfFiniteType f.left]
    (g : B ⟶ A) [IsMonHom g]
    (fd : BD ⟶ AD) (gd : AD ⟶ BD) [IsMonHom gd]
    (polarization : A ⟶ AD) [IsMonHom polarization]
    (hfg : f ≫ g = (𝟙 A : A ⟶ A) ^ n)
    (hfdgd : fd ≫ gd = (𝟙 BD : BD ⟶ BD) ^ n)
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme BD n).hom)
    (h_PoincareBundle : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ p : (Over.mk s ⟶ B) →* (Over.mk s ⟶ BD),
        ∀ a : Over.mk s ⟶ A,
          p (a ≫ f) ≫ fd = (a ≫ polarization) ^ n) :
    TorsionQuotient.SubgroupFunctor.torsionι B n ≫ (g ≫ polarization ≫ gd) = 1 := by
  have hi : TorsionQuotient.SubgroupFunctor.torsionι B n ^ n = 1 :=
    (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (TorsionQuotient.SubgroupFunctor.torsionι B n)).mp
      ⟨𝟙 _, Category.id_comp _⟩
  apply Geometric.Points.Construction.torsion_vanishing_of_geometric_points n (TorsionQuotient.SubgroupFunctor.torsionι B n) hi
    (g ≫ polarization ≫ gd) h_TorsionQuotient
  intro K hK hclosed s x
  obtain ⟨p, hp⟩ := h_PoincareBundle K s
  have hmultiple := candidate_is_multiple_on_points n f g fd gd polarization hfg hfdgd
    (Over.mk s) (Geometric.Points.Construction.surjective_on_geometric_points f K s) p hp (x ≫ TorsionQuotient.SubgroupFunctor.torsionι B n)
  have hx : (x ≫ TorsionQuotient.SubgroupFunctor.torsionι B n) ^ n = 1 := by
    rw [← MonObj.comp_pow, hi, MonObj.comp_one]
  calc
    (x ≫ TorsionQuotient.SubgroupFunctor.torsionι B n) ≫ (g ≫ polarization ≫ gd) =
        p (x ≫ TorsionQuotient.SubgroupFunctor.torsionι B n) ^ n := hmultiple
    _ = p ((x ≫ TorsionQuotient.SubgroupFunctor.torsionι B n) ^ n) := (p.map_pow _ n).symm
    _ = 1 := by rw [hx, p.map_one]

/-- A group-scheme homomorphism vanishing on B[n] is divisible by n,
provided multiplication by n is an fpqc morphism. -/
theorem divide_hom_by_multiplication
    (n : ℕ) (candidate : B ⟶ BD) [IsMonHom candidate]
    [Flat ((𝟙 B : B ⟶ B) ^ n).left]
    [Surjective ((𝟙 B : B ⟶ B) ^ n).left]
    [QuasiCompact ((𝟙 B : B ⟶ B) ^ n).left]
    (hkilled : TorsionQuotient.SubgroupFunctor.torsionι B n ≫ candidate = 1) :
    ∃! p : B ⟶ BD,
      IsMonHom p ∧ ((𝟙 B : B ⟶ B) ^ n) ≫ p = candidate := by
  have : IsMonHom ((𝟙 B : B ⟶ B) ^ n) := Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 B) n
  apply Picard.PoincareBundle.Epi.Construction.fpqc_group_hom_descent ((𝟙 B : B ⟶ B) ^ n) candidate
  intro T x hx
  have hxn : x ^ n = 1 := by
    simpa only [MonObj.comp_pow, Category.comp_id] using hx
  rw [← TorsionQuotient.SubgroupFunctor.torsionLift_ι n x hxn, Category.assoc, hkilled, MonObj.comp_one]

omit [IsCommMonObj A] [IsCommMonObj AD] in
/-- Relative construction of the homomorphism underlying the descended
polarization. No family-level descent hypothesis is used. -/
theorem relative_polarization_homomorphism
    (n : ℕ) (f : A ⟶ B) [IsMonHom f] [Epi f]
    [Surjective f.left] [LocallyOfFiniteType f.left]
    (g : B ⟶ A) [IsMonHom g]
    (fd : BD ⟶ AD) [IsMonHom fd]
    (gd : AD ⟶ BD) [IsMonHom gd]
    (polarization : A ⟶ AD) [IsMonHom polarization]
    (hfg : f ≫ g = (𝟙 A : A ⟶ A) ^ n)
    (hfdgd : fd ≫ gd = (𝟙 BD : BD ⟶ BD) ^ n)
    (hgdfd : gd ≫ fd = (𝟙 AD : AD ⟶ AD) ^ n)
    [Epi ((𝟙 A : A ⟶ A) ^ n)]
    [Flat ((𝟙 B : B ⟶ B) ^ n).left]
    [Surjective ((𝟙 B : B ⟶ B) ^ n).left]
    [QuasiCompact ((𝟙 B : B ⟶ B) ^ n).left]
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme BD n).hom)
    (h_PoincareBundle : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ p : (Over.mk s ⟶ B) →* (Over.mk s ⟶ BD),
        ∀ a : Over.mk s ⟶ A,
          p (a ≫ f) ≫ fd = (a ≫ polarization) ^ n) :
    ∃! p : B ⟶ BD,
      IsMonHom p ∧ f ≫ p ≫ fd = polarization ^ n := by
  let candidate := g ≫ polarization ≫ gd
  have hkilled : TorsionQuotient.SubgroupFunctor.torsionι B n ≫ candidate = 1 :=
    candidate_kills_torsion_of_TorsionQuotient_PoincareBundle n f g fd gd polarization hfg hfdgd h_TorsionQuotient h_PoincareBundle
  obtain ⟨p, ⟨hpHom, hp⟩, _⟩ := divide_hom_by_multiplication n candidate hkilled
  have : IsMonHom p := hpHom
  have : EffectiveEpi ((𝟙 B : B ⟶ B) ^ n) :=
    Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc _
  have hidentity : f ≫ p ≫ fd = polarization ^ n := by
    apply (cancel_epi ((𝟙 A : A ⟶ A) ^ n)).mp
    calc
      ((𝟙 A : A ⟶ A) ^ n) ≫ (f ≫ p ≫ fd) =
          f ≫ ((((𝟙 B : B ⟶ B) ^ n) ≫ p) ≫ fd) := by
            simp only [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp]
      _ = f ≫ candidate ≫ fd := by rw [hp]
      _ = ((𝟙 A : A ⟶ A) ^ n) ≫ (polarization ^ n) := by
        simp only [candidate, Category.assoc]
        rw [← Category.assoc f g, hfg]
        simp only [hgdfd, MonObj.comp_pow, Category.comp_id]
  refine ⟨p, ⟨hpHom, hidentity⟩, ?_⟩
  intro r hr
  have : IsMonHom r := hr.1
  exact polarization_pullback_injective n f fd gd hfdgd r p (hr.2.trans hidentity.symm)

end Relative

variable {S : Scheme.{u}} {A B AD BD : Over S}
  [GrpObj A] [GrpObj B] [GrpObj AD] [GrpObj BD]

/-- The constructed relative homomorphism agrees on every geometric fiber
with the field polarization supplied by PoincareBundle. Its positivity and type can
therefore be checked on those same field polarizations. -/
theorem relative_hom_matches_field_polarization
    (n : ℕ) (f : A ⟶ B) [IsMonHom f]
    [Surjective f.left] [LocallyOfFiniteType f.left]
    (fd : BD ⟶ AD) [IsMonHom fd] (gd : AD ⟶ BD) [IsMonHom gd]
    (polarization : A ⟶ AD)
    (hfdgd : fd ≫ gd = (𝟙 BD : BD ⟶ BD) ^ n)
    [Surjective ((𝟙 B : B ⟶ B) ^ n).left]
    [LocallyOfFiniteType ((𝟙 B : B ⟶ B) ^ n).left]
    (p : B ⟶ BD) [IsMonHom p]
    (hp : f ≫ p ≫ fd = polarization ^ n)
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (fieldPolarization : (Over.mk s ⟶ B) →* (Over.mk s ⟶ BD))
    (h_PoincareBundle : ∀ a : Over.mk s ⟶ A,
      fieldPolarization (a ≫ f) ≫ fd = (a ≫ polarization) ^ n) :
    IsMonHom.monoidHom p (Over.mk s) = fieldPolarization := by
  apply pullback_point_maps_injective
    (IsMonHom.monoidHom f (Over.mk s))
    (IsMonHom.monoidHom fd (Over.mk s))
    (IsMonHom.monoidHom gd (Over.mk s)) n
  · exact Geometric.Points.Construction.surjective_on_geometric_points f K s
  · simpa only [MonObj.comp_pow, Category.comp_id] using
      Geometric.Points.Construction.surjective_on_geometric_points ((𝟙 B : B ⟶ B) ^ n) K s
  · intro w
    change (w ≫ fd) ≫ gd = w ^ n
    rw [Category.assoc, hfdgd, MonObj.comp_pow, Category.comp_id]
  · intro a
    change (a ≫ f ≫ p) ≫ fd = fieldPolarization (a ≫ f) ≫ fd
    rw [h_PoincareBundle, Category.assoc, Category.assoc, hp, MonObj.comp_pow]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Polarization.Construction
