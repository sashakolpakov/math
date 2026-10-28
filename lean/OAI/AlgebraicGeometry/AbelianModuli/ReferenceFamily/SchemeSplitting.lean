import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Scheme Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeSplitting.EtaleSplitting

noncomputable section

/-! Construct etale neighborhoods trivializing any finite etale scheme,
including the actual abelian-scheme torsion kernel. This is a statement
about the original scheme and actual pullbacks, without a supplied frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} (X : Over S)

/-- A presentation of a pullback by an isomorphism supplies its Cartesian square. -/
theorem isPullback_of_overIso {T : Scheme} (u : T ⟶ S) (C : Over T)
    (e : C ≅ (Over.pullback u).obj X) :
    IsPullback (e.hom.left ≫ pullback.fst X.hom u) C.hom X.hom u := by
  have hw : e.hom.left ≫ pullback.snd X.hom u = C.hom := e.hom.w
  refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget T).mapIso e) rfl e.hom.w
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

/-- Over an affine base, the constructed algebra splitting gives a
scheme splitting over an etale neighborhood of each chosen point. -/
theorem exists_scheme_splitting_at_of_affine [IsAffine S] [IsFinite X.hom] [Etale X.hom]
    (s : S) :
    ∃ (T : Type) (_ : CommRing T) (u : Spec (.of T) ⟶ S),
      Etale u ∧ s ∈ Set.range u ∧ ∃ r : ℕ, Nonempty
        (HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of T)) (Fin r) ≅ (Over.pullback u).obj X) := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let R := Γ(S, ⊤)
  let B := Γ(X.left, ⊤)
  let : Algebra R B := X.hom.appTop.hom.toAlgebra
  have : Module.Finite R B := RingHom.finite_algebraMap.mp X.hom.finite_appTop
  have : Algebra.Etale R B := RingHom.etale_algebraMap.mp
    (HasRingHomProperty.appTop (P := @Etale) X.hom inferInstance)
  obtain ⟨T, _, u₀, hu₀, ⟨t, ht⟩, r, ⟨e⟩⟩ :=
    EtaleSplittingAt.EtaleSplitting.exists_affine_scheme_splitting_at R B (S.isoSpec.hom s)
  let u := u₀ ≫ S.isoSpec.inv
  have hu : Etale u := inferInstance
  let C := HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of T)) (Fin r)
  let a := e.hom.left ≫ pullback.fst (EtaleSplittingAt.EtaleSplitting.affineOver R B).hom u₀
  have hcart : IsPullback a C.hom (Spec.map X.hom.appTop) u₀ :=
    isPullback_of_overIso (EtaleSplittingAt.EtaleSplitting.affineOver R B) u₀ C e
  have hcart' : IsPullback (a ≫ X.left.isoSpec.inv) C.hom X.hom u :=
    hcart.of_iso (Iso.refl _) X.left.isoSpec.symm (Iso.refl _) S.isoSpec.symm
      (by simp) (by simp) (Scheme.isoSpec_inv_naturality X.hom) (by simp [u])
  refine ⟨T, inferInstance, u, hu, ⟨t, ?_⟩, r, ⟨?_⟩⟩
  · change S.isoSpec.inv (u₀ t) = s
    rw [ht]
    exact congrArg (fun f : S ⟶ S => f s) S.isoSpec.hom_inv_id
  · exact Over.isoMk hcart'.isoPullback hcart'.isoPullback_hom_snd

/-- Every finite etale scheme is locally a finite disjoint union of the
base, using constructed etale neighborhoods which jointly meet every point. -/
theorem exists_scheme_splitting_at [IsFinite X.hom] [Etale X.hom] (s : S) :
    ∃ (T : Type) (_ : CommRing T) (u : Spec (.of T) ⟶ S),
      Etale u ∧ s ∈ Set.range u ∧ ∃ r : ℕ, Nonempty
        (HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of T)) (Fin r) ≅ (Over.pullback u).obj X) := by
  obtain ⟨i, x, hx⟩ := S.affineCover.exists_eq s
  let v := S.affineCover.f i
  let Y := (Over.pullback v).obj X
  have : IsFinite Y.hom := inferInstanceAs (IsFinite (pullback.snd X.hom v))
  have : Etale Y.hom := inferInstanceAs (Etale (pullback.snd X.hom v))
  obtain ⟨T, _, u, hu, ⟨t, ht⟩, r, ⟨e⟩⟩ := exists_scheme_splitting_at_of_affine Y x
  refine ⟨T, inferInstance, u ≫ v, inferInstance, ⟨t, ?_⟩, r,
    ⟨e ≪≫ ((Over.pullbackComp u v).app X).symm⟩⟩
  change v (u t) = s
  rw [ht]
  exact hx

/-- The theorem applies directly to HilbertConstruction's actual torsion kernel and does
not require a level structure on the base. The finite set of labels here
still carries the transported torsion group law. -/
theorem exists_torsion_scheme_splitting_at {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    [IsFinite (A.torsionScheme N).hom] [Etale (A.torsionScheme N).hom] (s : S) :
    ∃ (T : Type) (_ : CommRing T) (u : Spec (.of T) ⟶ S),
      Etale u ∧ s ∈ Set.range u ∧ ∃ r : ℕ, Nonempty
        (HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of T)) (Fin r) ≅
          (Over.pullback u).obj (A.torsionScheme N)) :=
  exists_scheme_splitting_at (A.torsionScheme N) s

/-- Concrete local presentations, assembled only after the splitting
theorem has supplied them. -/
structure SplitCover where
  Index : Type
  source : Index → Scheme
  map : ∀ i, source i ⟶ S
  etale : ∀ i, Etale (map i)
  covers : ∀ s : S, ∃ i x, map i x = s
  rank : Index → ℕ
  presentation : ∀ i, HilbertConstruction.ConstantScheme.Iff.constantScheme (source i) (Fin (rank i)) ≅
    (Over.pullback (map i)).obj X

/-- The splitting cover is constructed from finite etaleness, with no
input marking and no preselected global trivialization. -/
def finiteEtaleSplitCover [IsFinite X.hom] [Etale X.hom] : SplitCover X := by
  have hex (s : S) := exists_scheme_splitting_at X s
  choose T hT u hu hp r he using hex
  letI (s : S) : CommRing (T s) := hT s
  exact {
    Index := S
    source := fun s => Spec (.of (T s))
    map := u
    etale := hu
    covers := fun s => ⟨s, hp s⟩
    rank := r
    presentation := fun s => Classical.choice (he s) }

namespace SplitCover

variable {X} (C : SplitCover X)

def total : Scheme := ∐ C.source

def projection : C.total ⟶ S := Sigma.desc C.map

/-- The disjoint union of the local neighborhoods is an etale cover. -/
theorem projection_etale : Etale C.projection := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := @RingHom.Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) C.etale

theorem projection_surjective : Surjective C.projection := by
  constructor
  intro s
  obtain ⟨i, x, hx⟩ := C.covers s
  refine ⟨Sigma.ι C.source i x, ?_⟩
  exact (congrArg (fun f : C.source i ⟶ S => f x) (Sigma.ι_comp_desc C.map i)).trans hx

end SplitCover

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeSplitting.EtaleSplitting
