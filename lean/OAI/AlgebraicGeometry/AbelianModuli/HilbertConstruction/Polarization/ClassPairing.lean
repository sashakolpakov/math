import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.PairSymmetry

/-! # Class Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ClassPairing

noncomputable section

/-! The polarization-induced Poincare pairing as an actual bilinear map
of bundle classes, together with its graph and product representatives. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {k : Type u} [Field k] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

def polarizationPairClass (T : Over (Spec (.of k))) :
    (T ⟶ A.scheme) →* ((T ⟶ A.scheme) →* Line.Bundles.LineBundle.IsoClass T.left) where
  toFun x := D.poincarePairClass T (x ≫ p)
  map_one' := by simp only [MonObj.one_comp, map_one]
  map_mul' x y := by simp only [MonObj.mul_comp, map_mul]

theorem polarizationPairClass_naturality {T U : Over (Spec (.of k))}
    (x y : T ⟶ A.scheme) (h : U ⟶ T) :
    Line.Bundles.LineBundle.pullbackClass h.left (polarizationPairClass D p T x y) =
      polarizationPairClass D p U (h ≫ x) (h ≫ y) := by
  change Line.Bundles.LineBundle.classOf ((D.poincarePair (x ≫ p) y).pullback h.left) =
    Line.Bundles.LineBundle.classOf (D.poincarePair ((h ≫ x) ≫ p) (h ≫ y))
  have he : Line.Bundles.LineBundle.classOf ((D.poincarePair (x ≫ p) y).pullback h.left) =
      Line.Bundles.LineBundle.classOf (D.poincarePair (h ≫ (x ≫ p)) (h ≫ y)) :=
    Quotient.sound ⟨D.poincarePairPullbackIso (x ≫ p) y h⟩
  simpa only [Category.assoc] using he

theorem graphPullback_class_eq_pair {T : Over (Spec (.of k))} (x : T ⟶ A.scheme) :
    Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback x.left) =
      polarizationPairClass D p T x x :=
  Quotient.sound ⟨D.poincareGraphPullbackPairIso p x⟩

theorem poincareAt_class_eq_pair_projections :
    Line.Bundles.LineBundle.classOf (D.poincareAt p) =
      polarizationPairClass D p (A.scheme ⊗ A.scheme) (fst A.scheme A.scheme) (snd A.scheme A.scheme) := by
  let z := lift (fst A.scheme A.scheme) (snd A.scheme A.scheme)
  have hz : z = 𝟙 (A.scheme ⊗ A.scheme) := lift_fst_snd
  let e : ((D.poincareAt p).pullback z.left).sheaf ≅ (D.poincareAt p).sheaf :=
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hz)).app (D.poincareAt p).sheaf ≪≫
      (Scheme.Modules.pullbackId (A.scheme ⊗ A.scheme).left).app (D.poincareAt p).sheaf
  exact Quotient.sound ⟨e.symm ≪≫
    PairSymmetry.poincareAt_pairPullbackIso D p (fst A.scheme A.scheme) (snd A.scheme A.scheme)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ClassPairing
