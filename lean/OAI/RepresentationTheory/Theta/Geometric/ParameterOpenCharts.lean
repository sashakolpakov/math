import OAI.RepresentationTheory.Theta.Geometric.ParameterBaseChange
import OAI.RepresentationTheory.Theta.Geometric.CommutingOpenMaps

/-! # Parameter Open Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.ParameterOpenCharts

noncomputable section

section

/-! Native affine charts on a family after an arbitrary change of
parameter algebra, including the maps between their coordinate rings. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {A : Type} [CommRing A] {Y : Scheme} (h : Y ⟶ Spec (.of A))

abbrev parameterProjection (R : Type) [CommRing R] [Algebra A R] : ParameterBaseChange.parameterBaseChange h R ⟶ Y :=
  pullback.fst _ _

abbrev parameterStructure (R : Type) [CommRing R] [Algebra A R] : ParameterBaseChange.parameterBaseChange h R ⟶ Spec (.of R) :=
  pullback.snd _ _

abbrev parameterOpen (R : Type) [CommRing R] [Algebra A R] (U : Y.Opens) :
    (ParameterBaseChange.parameterBaseChange h R).Opens := parameterProjection h R ⁻¹ᵁ U

def parameterOpenMap {R S : Type} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : S →ₐ[A] R) (U : Y.Opens) : (parameterOpen h R U).toScheme ⟶ (parameterOpen h S U).toScheme :=
  CommutingOpenMaps.commutingOpenMap (ParameterBaseChange.parameterBaseChangeMap h f) (parameterProjection h S) (parameterProjection h R)
    (ParameterBaseChange.parameterBaseChangeMap_fst h f) U

theorem parameterOpenMap_ι {R S : Type} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : S →ₐ[A] R) (U : Y.Opens) :
    parameterOpenMap h f U ≫ (parameterOpen h S U).ι =
      (parameterOpen h R U).ι ≫ ParameterBaseChange.parameterBaseChangeMap h f :=
  CommutingOpenMaps.commutingOpenMap_ι _ _ _ _ _

theorem parameterOpenMap_projection {R S : Type} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : S →ₐ[A] R) (U : Y.Opens) :
    parameterOpenMap h f U ≫ parameterProjection h S ∣_ U = parameterProjection h R ∣_ U :=
  CommutingOpenMaps.commutingOpenMap_projection _ _ _ _ _

theorem parameterOpenMap_structure {R S : Type} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : S →ₐ[A] R) (U : Y.Opens) :
    parameterOpenMap h f U ≫ ((parameterOpen h S U).ι ≫ parameterStructure h S) =
      ((parameterOpen h R U).ι ≫ parameterStructure h R) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Category.assoc, parameterOpenMap_ι, Category.assoc, ParameterBaseChange.parameterBaseChangeMap_snd, Category.assoc]

theorem parameterOpen_isPullback (R : Type) [CommRing R] [Algebra A R] (U : Y.Opens) :
    IsPullback (parameterProjection h R ∣_ U) ((parameterOpen h R U).ι ≫ parameterStructure h R)
      (U.ι ≫ h) (Spec.map (CommRingCat.ofHom (algebraMap A R))) :=
  (isPullback_morphismRestrict (parameterProjection h R) U).paste_vert (IsPullback.of_hasPullback _ _)

def parameterOpenCoordinateIso (R : Type) [CommRing R] [Algebra A R] (U : Y.Opens) (hU : IsAffineOpen U) :
    let : IsAffine U.toScheme := hU
    let : Algebra A Γ(U.toScheme, ⊤) := Affine.StructureCoordinates.affineStructureAlgebra (U.ι ≫ h)
    (parameterOpen h R U).toScheme ≅ Spec (.of (Γ(U.toScheme, ⊤) ⊗[A] R)) := by
  let : IsAffine U.toScheme := hU
  exact Affine.BaseChangeCoordinates.affineIsPullbackCoordinateIso (U.ι ≫ h) _ _ (parameterOpen_isPullback h R U)

theorem parameterOpenCoordinateIso_natural
    {R S : Type} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : S →ₐ[A] R) (U : Y.Opens) (hU : IsAffineOpen U) :
    let : IsAffine U.toScheme := hU
    let : Algebra A Γ(U.toScheme, ⊤) := Affine.StructureCoordinates.affineStructureAlgebra (U.ι ≫ h)
    (parameterOpenCoordinateIso h R U hU).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A Γ(U.toScheme, ⊤)) f).toRingHom) =
      parameterOpenMap h f U ≫ (parameterOpenCoordinateIso h S U hU).hom := by
  let : IsAffine U.toScheme := hU
  exact Affine.BaseChangeCoordinates.affineIsPullbackCoordinateIso_natural (U.ι ≫ h) f _ _ (parameterOpen_isPullback h R U)
    _ _ (parameterOpen_isPullback h S U) (parameterOpenMap h f U)
    (parameterOpenMap_projection h f U) (parameterOpenMap_structure h f U)

end

/-! Scalar transition equations on the actual family reflect through
an injected parameter algebra, using flatness of the family alone. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem commutingOpenMap_restrict {X Y Z : Scheme} (f : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ p = q) {U V : Z.Opens} (hVU : V ≤ U) :
    CommutingOpenMaps.commutingOpenMap f p q h V ≫ Y.homOfLE (p.preimage_mono hVU) =
      X.homOfLE (q.preimage_mono hVU) ≫ CommutingOpenMaps.commutingOpenMap f p q h U := by
  apply (cancel_mono (p ⁻¹ᵁ U).ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, CommutingOpenMaps.commutingOpenMap_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable {A R S : Type} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] {Y : Scheme} (h : Y ⟶ Spec (.of A))
    (f : S →ₐ[A] R)

theorem parameterOpenMap_dominant [Flat h] (hf : Function.Injective f) (U : Y.Opens) :
    IsSchemeTheoreticallyDominant (parameterOpenMap h f U) := by
  have : IsSchemeTheoreticallyDominant (ParameterBaseChange.parameterBaseChangeMap h f) := ParameterBaseChange.parameterBaseChangeMap_dominant h f hf
  have : QuasiCompact (ParameterBaseChange.parameterBaseChangeMap h f) := ParameterBaseChange.parameterBaseChangeMap_quasiCompact h f
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (CommutingOpenMaps.commutingOpenMap_isPullback (ParameterBaseChange.parameterBaseChangeMap h f) (parameterProjection h S)
      (parameterProjection h R) (ParameterBaseChange.parameterBaseChangeMap_fst h f) U).flip

theorem parameterOpenMap_quasiCompact (U : Y.Opens) : QuasiCompact (parameterOpenMap h f U) := by
  have : QuasiCompact (ParameterBaseChange.parameterBaseChangeMap h f) := ParameterBaseChange.parameterBaseChangeMap_quasiCompact h f
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (CommutingOpenMaps.commutingOpenMap_isPullback (ParameterBaseChange.parameterBaseChangeMap h f) (parameterProjection h S)
      (parameterProjection h R) (ParameterBaseChange.parameterBaseChangeMap_fst h f) U).flip
    (inferInstanceAs (QuasiCompact (ParameterBaseChange.parameterBaseChangeMap h f)))

theorem parameterOpenMap_base_section (U : Y.Opens) (a : Γ(U.toScheme, ⊤)) :
    (parameterOpenMap h f U).appTop ((parameterProjection h S ∣_ U).appTop a) =
      (parameterProjection h R ∣_ U).appTop a :=
  congrArg (fun t => t.appTop a) (parameterOpenMap_projection h f U)

theorem parameterOpenMap_restrict_section {U V : Y.Opens} (hVU : V ≤ U)
    (u : Γ((parameterOpen h S U).toScheme, ⊤)) :
    (parameterOpenMap h f V).appTop
        ((ParameterBaseChange.parameterBaseChange h S).homOfLE ((parameterProjection h S).preimage_mono hVU) |>.appTop u) =
      ((ParameterBaseChange.parameterBaseChange h R).homOfLE ((parameterProjection h R).preimage_mono hVU)).appTop
        ((parameterOpenMap h f U).appTop u) :=
  congrArg (fun t => t.appTop u) (commutingOpenMap_restrict (ParameterBaseChange.parameterBaseChangeMap h f)
    (parameterProjection h S) (parameterProjection h R) (ParameterBaseChange.parameterBaseChangeMap_fst h f) hVU)

theorem parameterOpen_transition_reflects [Flat h] (hf : Function.Injective f)
    (U V : Y.Opens) (a b : Γ((U ⊓ V).toScheme, ⊤))
    (u : Γ((parameterOpen h S U).toScheme, ⊤)) (v : Γ((parameterOpen h S V).toScheme, ⊤))
    (uR : Γ((parameterOpen h R U).toScheme, ⊤)) (vR : Γ((parameterOpen h R V).toScheme, ⊤))
    (hu : (parameterOpenMap h f U).appTop u = uR) (hv : (parameterOpenMap h f V).appTop v = vR)
    (hR : (parameterProjection h R ∣_ (U ⊓ V)).appTop a *
      ((ParameterBaseChange.parameterBaseChange h R).homOfLE ((parameterProjection h R).preimage_mono inf_le_left)).appTop uR =
        ((ParameterBaseChange.parameterBaseChange h R).homOfLE ((parameterProjection h R).preimage_mono inf_le_right)).appTop vR *
          (parameterProjection h R ∣_ (U ⊓ V)).appTop b) :
    (parameterProjection h S ∣_ (U ⊓ V)).appTop a *
      ((ParameterBaseChange.parameterBaseChange h S).homOfLE ((parameterProjection h S).preimage_mono inf_le_left)).appTop u =
        ((ParameterBaseChange.parameterBaseChange h S).homOfLE ((parameterProjection h S).preimage_mono inf_le_right)).appTop v *
          (parameterProjection h S ∣_ (U ⊓ V)).appTop b := by
  have : IsSchemeTheoreticallyDominant (parameterOpenMap h f (U ⊓ V)) := parameterOpenMap_dominant h f hf _
  have : QuasiCompact (parameterOpenMap h f (U ⊓ V)) := parameterOpenMap_quasiCompact h f _
  have hi : Function.Injective (parameterOpenMap h f (U ⊓ V)).appTop :=
    (parameterOpenMap h f (U ⊓ V)).app_injective ⊤
  apply hi
  rw [map_mul, map_mul, parameterOpenMap_base_section, parameterOpenMap_base_section,
    parameterOpenMap_restrict_section h f (show U ⊓ V ≤ U from inf_le_left),
    parameterOpenMap_restrict_section h f (show U ⊓ V ≤ V from inf_le_right), hu, hv]
  exact hR

end

end OAI.RepresentationTheory.Theta.Geometric.ParameterOpenCharts
