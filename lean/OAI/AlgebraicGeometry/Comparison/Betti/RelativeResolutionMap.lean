import OAI.AlgebraicGeometry.Comparison.Betti.RelativeQuotientMap
import OAI.AlgebraicGeometry.Comparison.Betti.FunctorialResolution

/-! # Relative Resolution Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RelativeResolutionMap

noncomputable section

section

/-! Iterate the original cokernel comparison through every stage of two functorial resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (T : C ⥤ C) (η : 𝟭 C ⟶ T) (S : D ⥤ D) (θ : 𝟭 D ⟶ S)
  (F : D ⥤ C) [F.Additive] (α : F ⋙ T ⟶ S ⋙ F)
  (hα : ∀ B, η.app (F.obj B) ≫ α.app B = F.map (θ.app B))

def residualComparison {A : C} {B : D} (u : A ⟶ F.obj B) :
    ∀ n, (FunctorialResolution.residualFunctor T η n).obj A ⟶ F.obj ((FunctorialResolution.residualFunctor S θ n).obj B)
  | 0 => u
  | n + 1 => RelativeQuotientMap.Resolution.relativeQuotientMap T η S θ F α hα (residualComparison u n)

theorem residualComparison_naturality {A A' : C} {B B' : D}
    (u : A ⟶ F.obj B) (u' : A' ⟶ F.obj B') (a : A ⟶ A') (b : B ⟶ B')
    (hu : a ≫ u' = u ≫ F.map b) (n : ℕ) :
    (FunctorialResolution.residualFunctor T η n).map a ≫ RelativeResolutionMap.residualComparison T η S θ F α hα u' n =
      RelativeResolutionMap.residualComparison T η S θ F α hα u n ≫ F.map ((FunctorialResolution.residualFunctor S θ n).map b) := by
  induction n with
  | zero => exact hu
  | succ n ih =>
      exact RelativeQuotientMap.Resolution.relativeQuotientMap_naturality T η S θ F α hα
        (RelativeResolutionMap.residualComparison T η S θ F α hα u n) (RelativeResolutionMap.residualComparison T η S θ F α hα u' n)
        ((FunctorialResolution.residualFunctor T η n).map a) ((FunctorialResolution.residualFunctor S θ n).map b) ih

def resolutionTermComparison {A : C} {B : D} (u : A ⟶ F.obj B) (n : ℕ) :
    (FunctorialResolution.resolutionTerm T η n).obj A ⟶ F.obj ((FunctorialResolution.resolutionTerm S θ n).obj B) :=
  T.map (RelativeResolutionMap.residualComparison T η S θ F α hα u n) ≫ α.app ((FunctorialResolution.residualFunctor S θ n).obj B)

theorem resolutionTermComparison_naturality {A A' : C} {B B' : D}
    (u : A ⟶ F.obj B) (u' : A' ⟶ F.obj B') (a : A ⟶ A') (b : B ⟶ B')
    (hu : a ≫ u' = u ≫ F.map b) (n : ℕ) :
    (FunctorialResolution.resolutionTerm T η n).map a ≫ resolutionTermComparison T η S θ F α hα u' n =
      resolutionTermComparison T η S θ F α hα u n ≫ F.map ((FunctorialResolution.resolutionTerm S θ n).map b) := by
  change T.map ((FunctorialResolution.residualFunctor T η n).map a) ≫
      (T.map (RelativeResolutionMap.residualComparison T η S θ F α hα u' n) ≫ α.app _) =
    (T.map (RelativeResolutionMap.residualComparison T η S θ F α hα u n) ≫ α.app _) ≫
      F.map (S.map ((FunctorialResolution.residualFunctor S θ n).map b))
  erw [← Category.assoc, ← T.map_comp, residualComparison_naturality T η S θ F α hα u u' a b hu n,
    T.map_comp, Category.assoc, α.naturality, ← Category.assoc]
  rfl

theorem resolutionTermComparison_unit {A : C} {B : D} (u : A ⟶ F.obj B) (n : ℕ) :
    η.app ((FunctorialResolution.residualFunctor T η n).obj A) ≫ resolutionTermComparison T η S θ F α hα u n =
      RelativeResolutionMap.residualComparison T η S θ F α hα u n ≫ F.map (θ.app ((FunctorialResolution.residualFunctor S θ n).obj B)) := by
  change η.app _ ≫ (T.map _ ≫ α.app _) = _
  rw [← Category.assoc, ← η.naturality, Category.assoc, hα]
  rfl

end

/-! The canonical relative cokernel maps assemble into an augmentation-preserving map of the actual resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (T : C ⥤ C) (η : 𝟭 C ⟶ T) (S : D ⥤ D) (θ : 𝟭 D ⟶ S)
  (F : D ⥤ C) [F.Additive] (α : F ⋙ T ⟶ S ⋙ F)
  (hα : ∀ B, η.app (F.obj B) ≫ α.app B = F.map (θ.app B))

theorem resolutionTermComparison_differential {A : C} {B : D} (u : A ⟶ F.obj B) (n : ℕ) :
    resolutionTermComparison T η S θ F α hα u n ≫ F.map ((FunctorialResolution.resolutionDifferential S θ n).app B) =
      (FunctorialResolution.resolutionDifferential T η n).app A ≫ resolutionTermComparison T η S θ F α hα u (n + 1) := by
  let An := (FunctorialResolution.residualFunctor T η n).obj A
  let Bn := (FunctorialResolution.residualFunctor S θ n).obj B
  let σ : An ⟶ F.obj Bn := RelativeResolutionMap.residualComparison T η S θ F α hα u n
  let σ' : cokernel (η.app An) ⟶ F.obj (cokernel (θ.app Bn)) :=
    RelativeResolutionMap.residualComparison T η S θ F α hα u (n + 1)
  let c' : T.obj (cokernel (η.app An)) ⟶ F.obj (S.obj (cokernel (θ.app Bn))) :=
    resolutionTermComparison T η S θ F α hα u (n + 1)
  have hπ : cokernel.π (η.app An) ≫ σ' =
      T.map σ ≫ α.app Bn ≫ F.map (cokernel.π (θ.app Bn)) :=
    RelativeQuotientMap.Resolution.relativeQuotientMap_π T η S θ F α hα σ
  have hunit : η.app (cokernel (η.app An)) ≫ c' = σ' ≫ F.map (θ.app (cokernel (θ.app Bn))) :=
    resolutionTermComparison_unit T η S θ F α hα u (n + 1)
  change (T.map σ ≫ α.app Bn) ≫
      F.map (cokernel.π (θ.app Bn) ≫ θ.app (cokernel (θ.app Bn))) =
    (cokernel.π (η.app An) ≫ η.app (cokernel (η.app An))) ≫ c'
  calc
    _ = (T.map σ ≫ α.app Bn ≫ F.map (cokernel.π (θ.app Bn))) ≫
        F.map (θ.app (cokernel (θ.app Bn))) := by
      rw [F.map_comp]
      exact (Category.assoc _ _ _).trans
        ((congrArg (T.map σ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
    _ = (cokernel.π (η.app An) ≫ σ') ≫ F.map (θ.app (cokernel (θ.app Bn))) :=
      congrArg (fun v => v ≫ F.map (θ.app (cokernel (θ.app Bn)))) hπ.symm
    _ = cokernel.π (η.app An) ≫ (η.app (cokernel (η.app An)) ≫ c') :=
      (Category.assoc _ _ _).trans (congrArg (cokernel.π (η.app An) ≫ ·) hunit.symm)
    _ = _ := (Category.assoc _ _ _).symm

def relativeResolutionMap {A : C} {B : D} (u : A ⟶ F.obj B) :
    FunctorialResolution.resolutionComplex T η A ⟶ (F.mapHomologicalComplex (.up ℕ)).obj (FunctorialResolution.resolutionComplex S θ B) where
  f n := resolutionTermComparison T η S θ F α hα u n
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    change resolutionTermComparison T η S θ F α hα u n ≫
        F.map ((FunctorialResolution.resolutionComplex S θ B).d n (n + 1)) =
      (FunctorialResolution.resolutionComplex T η A).d n (n + 1) ≫ resolutionTermComparison T η S θ F α hα u (n + 1)
    rw [FunctorialResolution.resolutionComplex_d, FunctorialResolution.resolutionComplex_d]
    exact resolutionTermComparison_differential T η S θ F α hα u n

theorem relativeResolutionMap_augmentation {A : C} {B : D} (u : A ⟶ F.obj B) :
    η.app A ≫ (relativeResolutionMap T η S θ F α hα u).f 0 = u ≫ F.map (θ.app B) :=
  resolutionTermComparison_unit T η S θ F α hα u 0

theorem relativeResolutionMap_naturality {A A' : C} {B B' : D}
    (u : A ⟶ F.obj B) (u' : A' ⟶ F.obj B') (a : A ⟶ A') (b : B ⟶ B')
    (hu : a ≫ u' = u ≫ F.map b) :
    FunctorialResolution.resolutionMap T η a ≫ relativeResolutionMap T η S θ F α hα u' =
      relativeResolutionMap T η S θ F α hα u ≫
        (F.mapHomologicalComplex (.up ℕ)).map (FunctorialResolution.resolutionMap S θ b) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact resolutionTermComparison_naturality T η S θ F α hα u u' a b hu n

end

end OAI.AlgebraicGeometry.Comparison.Betti.RelativeResolutionMap
