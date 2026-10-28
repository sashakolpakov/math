import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter

/-! # Quotient Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the universal property of the parameter-zero fiber

Quotienting by the image of an ideal gives the ring pushout. Applied to the
parameter ideal, this identifies the affine special fiber as a scheme
pullback, including its scheme structure.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Extension of an ideal and quotient form a pushout of commutative rings. -/
theorem quotient_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Ideal R) :
    IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map f.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map f.hom) f.hom
        (fun _ hx => Ideal.mem_map_of_mem _ hx))) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    ext x : 1
    rfl
  · intro T a b hab _
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom hab
  · intro T a b hab
    have hker : J.map f.hom ≤ RingHom.ker a.hom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change a (f x) = 0
      have h := ConcreteCategory.congr_hom hab x
      change a (f x) = b (Ideal.Quotient.mk J x) at h
      exact h.trans ((congrArg b (Ideal.Quotient.eq_zero_iff_mem.mpr hx)).trans
        b.hom.map_zero)
    refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift _ a.hom hker), ?_, ?_⟩
    · apply CommRingCat.hom_ext
      ext x : 1
      rfl
    · apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext x : 1
      exact ConcreteCategory.congr_hom hab x

/-- The quotient pushout with a specified, equal image ideal. -/
theorem quotient_isPushout_of_map_eq {R S : CommRingCat.{u}} (f : R ⟶ S)
    (J : Ideal R) (K : Ideal S) (hJK : J.map f.hom = K) :
    IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk K))
      (CommRingCat.ofHom (Ideal.quotientMap K f.hom
        (Ideal.map_le_iff_le_comap.mp hJK.le))) := by
  subst K
  exact quotient_isPushout f J

/-- The ideal defining zero in the actual parameter line. -/
def parameterZeroIdeal : Ideal (Polynomial (ULift.{u} ℤ)) := Ideal.span {Polynomial.X}

/-- The zero subscheme of the parameter line. -/
def parameterZeroBase : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal))

def parameterZeroInclusion : parameterZeroBase ⟶ Deformation.Parameter.BundleCycles.deformationParameterLine :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk parameterZeroIdeal))

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The parameter's zero ideal extends to precisely the deformation's special ideal. -/
theorem parameterZeroIdeal_map :
    parameterZeroIdeal.map (Deformation.Parameter.BundleCycles.deformationParameterRingMap I) = Deformation.Iff.BundleCycles.deformationSpecialIdeal I := by
  unfold parameterZeroIdeal Deformation.Iff.BundleCycles.deformationSpecialIdeal
  rw [Ideal.map_span, Set.image_singleton, Deformation.Parameter.BundleCycles.deformationParameterRingMap_X]

/-- The structural ring map of the special fiber over the zero subscheme. -/
def specialFiberToZeroRingMap :
    Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal →+* SpecialFiber.BundleCycles.DeformationSpecialRing I :=
  Ideal.quotientMap (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Parameter.BundleCycles.deformationParameterRingMap I)
    (Ideal.map_le_iff_le_comap.mp (parameterZeroIdeal_map I).le)

/-- The affine special fiber has the full universal property of the zero fiber. -/
theorem affineSpecialFiber_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I))))
      (Spec.map (CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing I) (specialFiberToZeroRingMap I)))
      (Spec.map (CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap I)))
      parameterZeroInclusion := by
  apply AlgebraicGeometry.isPullback_SpecMap_of_isPushout
  exact quotient_isPushout_of_map_eq
    (R := CommRingCat.of (Polynomial (ULift.{u} ℤ)))
    (S := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))
    (CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap I))
    parameterZeroIdeal (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (parameterZeroIdeal_map I)

variable {S : Type u} [CommRing S]

/-- The parameter-zero structure map commutes with coefficient homomorphisms. -/
theorem specialFiberToZeroRingMap_natural (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    (Deformation.Maps.BundleCycles.deformationSpecialMap I J f hf).comp (specialFiberToZeroRingMap I) =
      specialFiberToZeroRingMap J := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)
      (Deformation.Maps.BundleCycles.deformationMap I J f hf (Deformation.Parameter.BundleCycles.deformationParameterRingMap I p)) =
    Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J) (Deformation.Parameter.BundleCycles.deformationParameterRingMap J p)
  exact congrArg (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J))
    (RingHom.congr_fun (Deformation.Parameter.BundleCycles.deformationParameterRingMap_natural I J f hf) p)

variable {X : Scheme.{u}} (K : X.IdealSheafData)

/-- The compatible structural maps of all zero-fiber charts. -/
def specialFiberZeroCocone : Cocone (Global.SpecialFiber.BundleCycles.specialFiberGlueData K).functor where
  pt := parameterZeroBase
  ι.app U := Spec.map (CommRingCat.ofHom
    (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
    (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal U)) (specialFiberToZeroRingMap (K.ideal U)))
  ι.naturality {U V} f := by
    have h : CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal V)) (specialFiberToZeroRingMap (K.ideal V)) ≫
        (Global.SpecialFiber.BundleCycles.specialFiberDiagram K).map f.op =
      CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal U)) (specialFiberToZeroRingMap (K.ideal U)) := by
      apply CommRingCat.hom_ext
      exact specialFiberToZeroRingMap_natural (K.ideal V) (K.ideal U)
        (X.presheaf.map ((toOpensFunctor X).op.map f.op)).hom
        (K.ideal_le_comap_ideal (toOpens_mono f.le))
    exact (Spec.map_comp (CommRingCat.ofHom
      (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
      (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal V)) (specialFiberToZeroRingMap (K.ideal V)))
      ((Global.SpecialFiber.BundleCycles.specialFiberDiagram K).map f.op)).symm.trans (congrArg Spec.map h)

/-- The global special fiber's structure morphism to parameter zero. -/
def globalSpecialFiberToZero : Global.SpecialFiber.BundleCycles.globalSpecialFiber K ⟶ parameterZeroBase :=
  colimit.desc _ (specialFiberZeroCocone K)

theorem globalSpecialFiberToZero_on_chart (U : X.AffineZariskiSite) :
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover K).f U ≫ globalSpecialFiberToZero K =
      Spec.map (CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal U)) (specialFiberToZeroRingMap (K.ideal U))) :=
  colimit.ι_desc (specialFiberZeroCocone K) U

/-- Pullback squares descend from explicit pullback charts of an open cover. -/
theorem isPullback_of_cover_squares {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (k : B ⟶ D) (l : C ⟶ D)
    (V : B.OpenCover) (Z : V.I₀ → Scheme.{u})
    (a : ∀ i, Z i ⟶ A) (b : ∀ i, Z i ⟶ V.X i)
    (h : ∀ i, IsPullback (b i) (a i) (V.f i) f)
    (hs : ∀ i, IsPullback (b i) (a i ≫ g) (V.f i ≫ k) l) :
    IsPullback f g k l := by
  apply Scheme.isPullback_of_openCover f g k l V
  intro i
  let hi := (h i).flip
  apply (hs i).of_iso hi.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change b i ≫ 𝟙 (V.X i) = hi.isoPullback.hom ≫ pullback.snd f (V.f i)
    exact (Category.comp_id _).trans hi.isoPullback_hom_snd.symm
  · change (a i ≫ g) ≫ 𝟙 C = hi.isoPullback.hom ≫ (pullback.fst f (V.f i) ≫ g)
    exact (Category.comp_id _).trans
      ((congrArg (fun k => k ≫ g) hi.isoPullback_hom_fst.symm).trans (Category.assoc ..))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The globally glued cone is exactly the scheme-theoretic fiber at parameter zero. -/
theorem globalSpecialFiber_isPullback :
    IsPullback (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap K) (globalSpecialFiberToZero K)
      (Deformation.Parameter.BundleCycles.globalDeformationParameter K) parameterZeroInclusion := by
  apply isPullback_of_cover_squares (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap K) (globalSpecialFiberToZero K)
    (Deformation.Parameter.BundleCycles.globalDeformationParameter K) parameterZeroInclusion (Global.Deformation.BundleCycles.globalDeformationCover K)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover K).X (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover K).f
    (fun U => Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (K.ideal U)))))
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_chart_isPullback K)
  intro U
  have h := affineSpecialFiber_isPullback (K.ideal U)
  rw [← globalSpecialFiberToZero_on_chart K U, ← Deformation.Parameter.BundleCycles.globalDeformationParameter_on_chart K U] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber.BundleCycles
