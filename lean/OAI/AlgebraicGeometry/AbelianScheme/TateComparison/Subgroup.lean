import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Finite-etale subgroup models and geometric elementary types are
preserved by actual base changes and group-scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S S' : Scheme.{u}} {g : ℕ}

def Subgroup.pullbackPointsEquiv (A : Over S) (s : S' ⟶ S) (T : Over S') :
    (T ⟶ (Over.pullback s).obj A) ≃ ((Over.map s).obj T ⟶ A) :=
  ((Over.mapPullbackAdj s).homEquiv T A).symm

theorem Subgroup.pullbackPointsEquiv_map {A B : Over S} (f : A ⟶ B) (s : S' ⟶ S)
    (T : Over S') (x : T ⟶ (Over.pullback s).obj A) :
    TateComparison.Subgroup.pullbackPointsEquiv B s T (x ≫ (Over.pullback s).map f) =
      TateComparison.Subgroup.pullbackPointsEquiv A s T x ≫ f := by
  apply Over.OverMorphism.ext
  change (x.left ≫ ((Over.pullback s).map f).left) ≫ pullback.fst B.hom s =
    (x.left ≫ pullback.fst A.hom s) ≫ f.left
  rw [Category.assoc, AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc]

def Subgroup.subgroupComapEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (F : Subgroup H) :
    F.comap e.toMonoidHom ≃* F where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by
    change e (e.symm y.val) ∈ F
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

def Subgroup.groupIsoPoints {A B : Over S} [GrpObj A] [GrpObj B]
    (e : A ≅ B) [IsMonHom e.hom] (T : Over S) : (T ⟶ A) ≃* (T ⟶ B) where
  toFun x := x ≫ e.hom
  invFun y := y ≫ e.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.mul_comp x y e.hom

variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem Subgroups.PointSubgroup.comapHom_congr (F : Subgroups.PointSubgroup B) (f h : A.scheme ⟶ B.scheme)
    [IsMonHom f] [IsMonHom h] (w : f = h) : F.comapHom f = F.comapHom h := by
  subst h
  rfl

theorem Subgroups.PointSubgroup.hasFiniteEtaleModel_pullback (F : Subgroups.PointSubgroup A) (hF : F.HasFiniteEtaleModel)
    (s : S' ⟶ S) : (F.pullback s).HasFiniteEtaleModel := by
  obtain ⟨H, i, hiGroup, hiMono, hfinite, hetale, hmodel⟩ := hF
  let : IsMonHom i := hiGroup
  let : Mono i := hiMono
  let : IsFinite H.X.hom := hfinite
  let : Etale H.X.hom := hetale
  let H' := BaseChange.baseChangedGroup H.X s
  let i' : H'.X ⟶ (A.pullback s).scheme := (Over.pullback s).map i
  refine ⟨H', i', inferInstanceAs (IsMonHom ((Over.pullback s).map i)),
    inferInstanceAs (Mono ((Over.pullback s).map i)), ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsFinite (pullback.snd H.X.hom s))
  · exact inferInstanceAs (Etale (pullback.snd H.X.hom s))
  · intro T x
    change TateComparison.Subgroup.pullbackPointsEquiv A.scheme s T x ∈ F.atTest ((Over.map s).obj T) ↔ _
    rw [hmodel]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(TateComparison.Subgroup.pullbackPointsEquiv H.X s T).symm y, ?_⟩
      apply (TateComparison.Subgroup.pullbackPointsEquiv A.scheme s T).injective
      exact (TateComparison.Subgroup.pullbackPointsEquiv_map i s T ((TateComparison.Subgroup.pullbackPointsEquiv H.X s T).symm y)).trans
        ((congrArg (fun z => z ≫ i) ((TateComparison.Subgroup.pullbackPointsEquiv H.X s T).apply_symm_apply y)).trans hy)
    · rintro ⟨y, rfl⟩
      exact ⟨TateComparison.Subgroup.pullbackPointsEquiv H.X s T y, (TateComparison.Subgroup.pullbackPointsEquiv_map i s T y).symm⟩

theorem Subgroups.PointSubgroup.hasGeometricType_pullback (F : Subgroups.PointSubgroup A) {q : ℕ} {a : Fin 3 → ℕ}
    (hF : F.HasGeometricType q a) (s : S' ⟶ S) : (F.pullback s).HasGeometricType q a := by
  intro k _ _ t
  obtain ⟨e⟩ := hF k (t ≫ s)
  exact ⟨(TateComparison.Subgroup.subgroupComapEquiv (A.baseChangePointsMulEquiv s (Over.mk t))
    (F.atTest ((Over.map s).obj (Over.mk t)))).trans e⟩

theorem Subgroups.PointSubgroup.hasFiniteEtaleModel_comapIso (F : Subgroups.PointSubgroup B) (hF : F.HasFiniteEtaleModel)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : (F.comapHom e.hom).HasFiniteEtaleModel := by
  obtain ⟨H, i, hiGroup, hiMono, hfinite, hetale, hmodel⟩ := hF
  let : IsMonHom i := hiGroup
  let : Mono i := hiMono
  refine ⟨H, i ≫ e.inv, inferInstance, inferInstance, hfinite, hetale, ?_⟩
  intro T x
  change x ≫ e.hom ∈ F.atTest T ↔ _
  rw [hmodel]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← Category.assoc, hy]
    simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← hy]
    simp

theorem Subgroups.PointSubgroup.hasGeometricType_comapIso (F : Subgroups.PointSubgroup B) {q : ℕ} {a : Fin 3 → ℕ}
    (hF : F.HasGeometricType q a) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (F.comapHom e.hom).HasGeometricType q a := by
  intro k _ _ t
  obtain ⟨h⟩ := hF k t
  exact ⟨(TateComparison.Subgroup.subgroupComapEquiv (TateComparison.Subgroup.groupIsoPoints e (Over.mk t)) (F.atTest (Over.mk t))).trans h⟩

theorem Subgroups.PointSubgroup.pullback_inf (F G : Subgroups.PointSubgroup A) (s : S' ⟶ S) :
    (F.inf G).pullback s = (F.pullback s).inf (G.pullback s) := by
  apply Subgroups.PointSubgroup.ext
  intro T
  rfl

theorem Subgroups.PointSubgroup.pullback_kernel (f : A.scheme ⟶ B.scheme) [IsMonHom f] (s : S' ⟶ S) :
    (Subgroups.PointSubgroup.kernel f).pullback s = @Subgroups.PointSubgroup.kernel S' g
      (A.pullback s) (B.pullback s) ((Over.pullback s).map f)
        (inferInstanceAs (IsMonHom ((Over.pullback s).map f))) := by
  apply Subgroups.PointSubgroup.ext
  intro T
  ext x
  change A.baseChangePointsEquiv s T x ≫ f = 1 ↔ x ≫ (Over.pullback s).map f = 1
  rw [← AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map]
  exact (B.baseChangePointsMulEquiv s T).map_eq_one_iff

theorem Subgroups.PointSubgroup.comap_inf (F G : Subgroups.PointSubgroup B) (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (F.inf G).comapHom f = (F.comapHom f).inf (G.comapHom f) := by
  apply Subgroups.PointSubgroup.ext
  intro T
  rfl

theorem Subgroups.PointSubgroup.kernel_comp_right_iso {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (e : B.scheme ≅ C.scheme) [IsMonHom e.hom] :
    Subgroups.PointSubgroup.kernel (f ≫ e.hom) = Subgroups.PointSubgroup.kernel f := by
  apply Subgroups.PointSubgroup.ext
  intro T
  ext x
  change x ≫ (f ≫ e.hom) = 1 ↔ x ≫ f = 1
  rw [← Category.assoc, ← (TateComparison.Subgroup.groupIsoPoints e T).map_one]
  exact (TateComparison.Subgroup.groupIsoPoints e T).injective.eq_iff

theorem Subgroups.PointSubgroup.kernel_comp_left {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (h : B.scheme ⟶ C.scheme) [IsMonHom h] :
    Subgroups.PointSubgroup.kernel (f ≫ h) = (Subgroups.PointSubgroup.kernel h).comapHom f := by
  apply Subgroups.PointSubgroup.ext
  intro T
  ext x
  change x ≫ (f ≫ h) = 1 ↔ (x ≫ f) ≫ h = 1
  rw [Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
