import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineSpecialFiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Component Lift -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ComponentLift.Components

noncomputable section

/-!
Constructing the integral component map from its native special fiber.
Finite schemes supply their affine presentations; HenselianLifting supplies the map.
Uniqueness forces the group law, so no integral component projection or
integral group-homomorphism property is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

omit [HenselianLocalRing R] in
theorem finite_coordinates_of_iso {A : Type u} [CommRing A] [Algebra R A]
    {X : Over (Spec (.of R))} [IsFinite X.hom] (e : EtaleTargetMaps.Components.affineOver R A ≅ X) :
    Module.Finite R A := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map e.hom))
  have h : IsFinite (EtaleTargetMaps.Components.affineOver R A).hom := by
    rw [← e.hom.w]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h)

omit [HenselianLocalRing R] in
theorem etale_coordinates_of_iso {A : Type u} [CommRing A] [Algebra R A]
    {X : Over (Spec (.of R))} [Etale X.hom] (e : EtaleTargetMaps.Components.affineOver R A ≅ X) :
    Algebra.Etale R A := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map e.hom))
  have h : Etale (EtaleTargetMaps.Components.affineOver R A).hom := by
    rw [← e.hom.w]
    infer_instance
  exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h)

/-- Native special-fiber maps from a finite scheme to a finite etale
scheme lift uniquely. The source is allowed to have connected torsion. -/
theorem finite_etale_special_fiber_hom_bijective
    (X E : Over (Spec (.of R))) [IsFinite X.hom] [IsFinite E.hom] [Etale E.hom] :
    Function.Bijective
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
        (X := X) (Y := E)) := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have hX : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have hE : IsAffine E.left := isAffine_of_isAffineHom E.hom
  obtain ⟨A, ⟨eA⟩⟩ := (essImage_algSpec (R := .of R) (G := X)).mpr hX
  obtain ⟨C, ⟨eC⟩⟩ := (essImage_algSpec (R := .of R) (G := E)).mpr hE
  change EtaleTargetMaps.Components.affineOver R A.unop ≅ X at eA
  change EtaleTargetMaps.Components.affineOver R C.unop ≅ E at eC
  have : Module.Finite R A.unop := finite_coordinates_of_iso R eA
  have : Module.Finite R C.unop := finite_coordinates_of_iso R eC
  have : Algebra.Etale R C.unop := etale_coordinates_of_iso R eC
  have hb := AffineSpecialFiber.Components.affine_special_fiber_hom_bijective (R := R) (A := A.unop) (C := C.unop)
  constructor
  · intro f g h
    change F.map f = F.map g at h
    have hfg : eA.hom ≫ f ≫ eC.inv = eA.hom ≫ g ≫ eC.inv := by
      apply hb.1
      change F.map (eA.hom ≫ f ≫ eC.inv) = F.map (eA.hom ≫ g ≫ eC.inv)
      simpa only [F.map_comp] using congrArg (fun a => F.map eA.hom ≫ a ≫ F.map eC.inv) h
    exact (cancel_epi eA.hom).mp ((cancel_mono eC.inv).mp (by simpa only [Category.assoc] using hfg))
  · intro φ
    obtain ⟨g, hg⟩ := hb.2 (F.map eA.hom ≫ φ ≫ F.map eC.inv)
    change F.map g = F.map eA.hom ≫ φ ≫ F.map eC.inv at hg
    refine ⟨eA.inv ≫ g ≫ eC.hom, ?_⟩
    change F.map (eA.inv ≫ g ≫ eC.hom) = φ
    rw [F.map_comp, F.map_comp, hg]
    rw [← Category.assoc, ← Category.assoc, ← F.map_comp, eA.inv_hom_id,
      F.map_id, Category.id_comp, Category.assoc, ← F.map_comp, eC.inv_hom_id,
      F.map_id, Category.comp_id]

/-- The group law of a lifted component map is a consequence of its
special-fiber group law and the uniqueness theorem for finite sources. -/
theorem isMonHom_of_special_fiber
    {A E : Over (Spec (.of R))} [GrpObj A] [GrpObj E]
    [IsFinite A.hom] [IsFinite E.hom] [Etale E.hom]
    (f : A ⟶ E)
    (hf : IsMonHom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f)) :
    IsMonHom f := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have : IsMonHom (F.map f) := hf
  have : IsFinite (𝟙_ (Over (Spec (.of R)))).hom := by
    dsimp
    infer_instance
  have : IsFinite (A ⊗ A).hom := by
    dsimp
    infer_instance
  constructor
  · apply (finite_etale_special_fiber_hom_bijective R (𝟙_ _) E).1
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    simpa only [Functor.map_comp, Category.assoc, Functor.obj.η_def]
      using (IsMonHom.one_hom (F.map f))
  · apply (finite_etale_special_fiber_hom_bijective R (A ⊗ A) E).1
    apply (cancel_epi (Functor.LaxMonoidal.μ F A A)).mp
    simpa only [Functor.map_comp, Category.assoc, Functor.obj.μ_def,
      Functor.LaxMonoidal.μ_natural_assoc]
      using (IsMonHom.mul_hom (F.map f))

variable {A E : Over (Spec (.of R))} [GrpObj A] [GrpObj E]
variable [IsFinite A.hom] [IsFinite E.hom] [Etale E.hom]

/-- The integral projection to the etale component scheme is constructed
from the independently given projection on the special fiber. -/
def nativeComponentMap
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E) : A ⟶ E :=
  Classical.choose ((finite_etale_special_fiber_hom_bijective R A E).2 π₀)

omit [GrpObj A] [GrpObj E] in
theorem nativeComponentMap_special
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
      (nativeComponentMap R π₀) = π₀ :=
  Classical.choose_spec ((finite_etale_special_fiber_hom_bijective R A E).2 π₀)

instance nativeComponentMap_isMonHom
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E)
    [IsMonHom π₀] : IsMonHom (nativeComponentMap R π₀) := by
  apply isMonHom_of_special_fiber R
  rw [nativeComponentMap_special]
  infer_instance

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ComponentLift.Components
