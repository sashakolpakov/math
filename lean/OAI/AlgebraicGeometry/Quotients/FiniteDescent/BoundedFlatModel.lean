import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainPrepend

/-! # Bounded Flat Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BoundedFlatModel

noncomputable section

/-! A bounded flat complex with finite positive cohomology has a universally
quasi-isomorphic model with finite free positive terms and a flat first term. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.CochainFiniteModel

variable {R : Type u} [CommRing R]

def identity (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ n, Module.Flat R (C.X n))
    (hfinite : ∀ n, Module.Finite R (C.X (n + 1)))
    (hfree : ∀ n, Module.Free R (C.X (n + 1)))
    (hbound : ∃ N, ∀ q, N ≤ q → IsZero (C.X q)) : CochainModel.Construction.CochainFiniteModel.Model C where
  complex := C
  comparison := 𝟙 C
  quasiIso := inferInstance
  flat := hflat
  finite := hfinite
  free := hfree
  bounded := hbound
  tensor_quasiIso A _ _ := by
    change QuasiIso (((ModuleTensor.Construction.ModuleTensorFunctor.tensor A).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (𝟙 C))
    infer_instance

variable [IsNoetherianRing R]

def prepend (C : CochainComplex (ModuleCat.{u} R) ℕ) (M : CochainModel.Construction.CochainFiniteModel.Model (CochainHeadD.Construction.CochainHead.tail C))
    [Module.Flat R (C.X 0)] [Module.Finite R (C.homology 1)] : CochainModel.Construction.CochainFiniteModel.Model C := by
  have := M.quasiIso
  let d := CochainZero.Construction.CochainZeroCycles.lift M.comparison (C.d 0 1)
    (by rw [CochainHeadD.Construction.CochainHead.tail_d]; exact C.d_comp_d _ _ _)
  have hd : d ≫ M.complex.d 0 1 = 0 := CochainZero.Construction.CochainZeroCycles.lift_zero _ _ _
  have h : 𝟙 (C.X 0) ≫ C.d 0 1 = d ≫ M.comparison.f 0 := by
    rw [Category.id_comp]
    exact (CochainZero.Construction.CochainZeroCycles.lift_comp M.comparison (C.d 0 1)
      (by rw [CochainHeadD.Construction.CochainHead.tail_d]; exact C.d_comp_d _ _ _)).symm
  let E := CochainHeadD.Construction.CochainHead.cons (C.X 0) M.complex d hd
  let e := CochainHeadD.Construction.CochainHead.consMap (𝟙 (C.X 0)) M.comparison d (C.d 0 1) hd
    (by rw [CochainHeadD.Construction.CochainHead.tail_d]; exact C.d_comp_d _ _ _) h
  have : QuasiIso e := CochainPrepend.Construction.CochainPrependComparison.quasiIso _ _ _ _ _ _
  let φ : E ⟶ C := e ≫ (CochainHeadD.Construction.CochainHead.consTailIso C).hom
  have : QuasiIso φ := inferInstanceAs (QuasiIso (e ≫ (CochainHeadD.Construction.CochainHead.consTailIso C).hom))
  apply CochainModel.Construction.CochainFiniteModel.improve φ
  · intro n
    cases n with
    | zero => exact inferInstanceAs (Module.Flat R (C.X 0))
    | succ n => exact M.flat n
  · intro n
    exact M.finite n
  · intro n
    exact M.free n
  · obtain ⟨N, hN⟩ := M.bounded
    refine ⟨N + 1, fun q hq => ?_⟩
    cases q with
    | zero => omega
    | succ q => exact hN q (Nat.le_of_succ_le_succ hq)
  · intro A _ _
    have := M.tensor_quasiIso A
    have : QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A e) :=
      CochainPrepend.Construction.CochainPrependComparison.mapped_quasiIso _ _ _ _ _ _ (ModuleTensor.Construction.ModuleTensorFunctor.tensor A)
    change QuasiIso (((ModuleTensor.Construction.ModuleTensorFunctor.tensor A).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (e ≫ (CochainHeadD.Construction.CochainHead.consTailIso C).hom))
    rw [Functor.map_comp]
    infer_instance

theorem exists_model (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (hbound : ∀ q, n ≤ q → IsZero (C.X q))
    (hflat : ∀ q, Module.Flat R (C.X q))
    (hfinite : ∀ q, Module.Finite R (C.homology (q + 1))) : Nonempty (CochainModel.Construction.CochainFiniteModel.Model C) := by
  induction n generalizing C with
  | zero =>
      have hs : ∀ q, Subsingleton (C.X (q + 1)) := fun q =>
        ModuleCat.isZero_iff_subsingleton.mp (hbound (q + 1) (Nat.zero_le _))
      exact ⟨identity C hflat (fun q => by have := hs q; infer_instance)
        (fun q => by have := hs q; infer_instance) ⟨0, hbound⟩⟩
  | succ n ih =>
      have htbound : ∀ q, n ≤ q → IsZero ((CochainHeadD.Construction.CochainHead.tail C).X q) := fun q hq =>
        hbound (q + 1) (Nat.add_le_add_right hq 1)
      have htflat : ∀ q, Module.Flat R ((CochainHeadD.Construction.CochainHead.tail C).X q) := fun q => hflat (q + 1)
      have htfinite : ∀ q, Module.Finite R ((CochainHeadD.Construction.CochainHead.tail C).homology (q + 1)) := by
        intro q
        have := hfinite (q + 1)
        exact Module.Finite.equiv (CochainHeadCohomology.Construction.CochainHead.tailHomologyIso C q).symm.toLinearEquiv
      obtain ⟨M⟩ := ih (CochainHeadD.Construction.CochainHead.tail C) htbound htflat htfinite
      have := hflat 0
      have := hfinite 0
      exact ⟨prepend C M⟩

end Construction.CochainFiniteModel

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BoundedFlatModel
