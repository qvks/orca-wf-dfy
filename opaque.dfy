/*
 * Var naming convention:
 * a: ActorAddr
 * i: Addr
 * c: Config
 * st: State
 */
abstract module Opaque{
    ////CONFIG////
    type Config
    type Actor
    type Frame
    datatype Msg = orca(i: Addr, z: int) | app(f: Frame) | ERR
    function Heap(c: Config, i: Addr, fid: FId) : Addr
    function allocated_addresses(c: Config) : set<Addr>

    ////IDs////
    type FId
    type BId
    type ClassId
    type VarId

    ////ADDRESSES////
    datatype Addr = OA(ObjectAddr) | AA(ActorAddr) | Null
    type ObjectAddr
    type ActorAddr

    ////PATHS////
    datatype Capability = WRITE | READ | TAG | ERR
    type DP
    type SP

    datatype Optional<T> = Some(o: T) | None

    ////ACTORS////
    //lemma all valid actor addresses are in the domain of Actors
    function Actors(c: Config, a: ActorAddr) : Actor

    //Queues//
    function queue_length(c: Config, a: ActorAddr) : nat
    function queue_n(c: Config, a: ActorAddr, n: nat) : Msg

    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then queue_n(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue(c: Config, a: ActorAddr) {
        (forall n: nat :: n < queue_length(c,a) ==> queue_n(c, a, n) != Msg.ERR) &&
        (forall n: nat :: n >= queue_length(c,a) ==> queue_n(c,a,n) == Msg.ERR)
    }

    predicate push(c: Config, a: ActorAddr, msg: Msg, c': Config)
    {
        WF_queue(c, a) &&
        msg != Msg.ERR &&
        queue_length(c', a) == queue_length(c, a) + 1 &&
        queue_n(c', a, queue_length(c,a)) == msg &&
        (forall n: nat :: n != queue_length(c,a) ==>
        queue_n(c', a, n) == queue_n(c, a, n))
    }

    lemma {:verify false} push_preserves_WF_queue(c: Config, a: ActorAddr, msg: Msg, c': Config)
        requires push(c, a, msg, c')
        ensures WF_queue(c', a)
    {
    }

    predicate pop(c:Config, a:ActorAddr, c': Config)
    {
        WF_queue(c, a) &&
        queue_length(c', a) == queue_length(c, a) - 1 &&
        forall n: nat :: n >= 0 ==>
        queue_n(c', a, n) == queue_n(c, a, n+1)
    }

    lemma {:verify false} pop_preserves_WF_queue(c: Config, a: ActorAddr, c': Config)
        requires pop(c, a, c')
        ensures WF_queue(c', a)
    {
    }

    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : nat
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int
    //{|(set x | exists a,k :: 0<=k<queue_length(c, a) && x==(a,k) && Reach(c,a,k,i))|}

    predicate A(c: Config, a: ActorAddr, dp: DP, i: Addr, k: Capability)

    ////DATA RACE FREEDOM////
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr, k: Capability::
            a != a' &&
            A(c, a, p, i, WRITE) &&
            A(c, a', p', i, k) ==>
            k == TAG
    }

    ////INVARIANTS////
    predicate INV_2(c: Config) {
        forall i, dp, mp, k, a, a_own ::
            (A(c, a, dp, i, k) &&
            !Owner(c, i, a)) ||
            (A(c, a_own, mp, i, k) &&
            Owner(c, i, a_own) &&
            is_a_message_path(c, mp)) ==>
            LRC(c, i) > 0

    }
    predicate is_a_message_path(c: Config, mp: DP)

    predicate INV_3(c: Config) {
        forall i, dp, k, a ::
            A(c, a, dp, i, k) &&
            !Owner(c, i, a) ==>
            RC(c, i, a) > 0
    }




    ///////////////PSEUDO CODE FOR RECEIVING MESSAGES (FIGURE 6)///////////////

    ////RcvApp////
    predicate RcvApp(c: Config, a: ActorAddr, c': Config)
        requires actor_state_idle(c, a)
        requires queue_head_app(c, a)
    {
        actor_state_rcv(c', a) &&
        //0 here, 1 in the paper, leave which one?
        actor_ws(c', a) == set i |
            i in allocated_addresses(c) &&
            exists mp,k ::
            mp in paths_from_message_n(c, a, 0) &&
            A(c,a,mp,i,k)
    }

    predicate Ownership_Immutable(c: Config, c': Config)
    {
        forall i, a' :: Owner(c,i,a') == Owner(c',i,a')
    }

    predicate RcvToExe(c: Config, a: ActorAddr, c': Config)
    {
        actor_state_rcv(c, a) &&
        queue_head_app(c, a) &&
        actor_state_exe(c', a) &&
        actor_state_exe_frame(c', a) == frame_from_app_message_n(c,a,0) &&
        pop(c, a, c') &&
        (forall i :: i in actor_ws(c,a) && Owner(c, i, a) ==> RC(c', i, a) == RC(c, i, a) - 1) &&
        (forall i :: i in actor_ws(c,a) && !Owner(c, i, a) ==> RC(c', i, a) == RC(c, i, a) + 1) &&
        (forall i :: i !in actor_ws(c,a) ==> RC(c', i, a) == RC(c, i, a)) &&
        Ownership_Immutable(c, c') &&
        (forall i, a' :: a' != a ==> RC(c', i, a') == RC(c, i, a'))
    }

    lemma {:verify true} RcvToExe_Increases_A(c: Config, a: ActorAddr, c': Config)
        requires RcvToExe(c, a, c')
        ensures forall lp, i, k :: A(c, a, lp, i, k) ==> A(c', a, lp, i, k)
        ensures forall lp, i, k :: A(c', a, lp, i, k) ==> A(c, a, lp, i, k) || i in actor_ws(c, a)
        ensures forall lp, i, k, a' :: a' != a ==> A(c', a', lp, i, k) == A(c, a', lp, i, k)


    lemma {:verify true} RcvToExe_Preserves_INV_3(c: Config, a': ActorAddr, c': Config)
        requires INV_3(c)
        requires RcvToExe(c, a', c')
        ensures INV_3(c')
    {
        RcvToExe_Increases_A(c, a', c');
        forall i, lp, k, a |
            A(c', a, lp, i, k) &&
            !Owner(c', i ,a)
            ensures RC(c', i, a) > 0
        {
            if a' == a && i in actor_ws(c, a) {
                assert RC(c, i, a) >= 0;
                assert RC(c', i, a) == RC(c, i, a) + 1;
            } else {
                assert RC(c', i, a) == RC(c, i, a);
                assert RC(c, i, a) > 0;
                assert RC(c', i, a) > 0;
            }
        }
    }

    ////AUXILIARY FOR RcvApp////
    predicate actor_state_idle(c: Config, a: ActorAddr)

    predicate queue_head_app(c: Config, a: ActorAddr)
        ensures queue_length(c, a) > 0

    predicate actor_state_rcv(c: Config, a: ActorAddr)

    function paths_from_message_n(c: Config, a: ActorAddr, n: nat) : set<DP>
        requires n < queue_length(c, a)

    function actor_ws(c: Config, a: ActorAddr) : set<Addr>
        requires actor_state_rcv(c, a)

    function queue_head_iotas(c: Config, a: ActorAddr) : set<Addr>
        requires queue_head_app(c, a)

    predicate Owner(c: Config, i: Addr, a: ActorAddr)

    predicate actor_state_exe(c: Config, a: ActorAddr)

    function actor_state_exe_frame(c: Config, a: ActorAddr) : Frame

    function frame_from_app_message_n(c: Config, a: ActorAddr, n: nat) : Frame

    ///////////////PSEUDO CODE FOR RECEIVING AN ORCA MESSAGE (FIGURE 7)///////////////


    ////AUXILIARY FOR INV_6////
    predicate queue_at_n_orca(c: Config, a: ActorAddr, n: nat)
        ensures queue_at_n_orca(c, a, n) ==> n <= queue_length(c, a)
    {
        WF_queue(c, a) &&
        queue_n(c, a, n).orca?
    }

    function queue_at_n_orca_i(c: Config, a: ActorAddr, n: nat) : Addr
        requires queue_at_n_orca(c, a, n)
    {
        queue_n(c, a, n).i
    }
    function queue_at_n_orca_z(c: Config, a: ActorAddr, n: nat) : int
        requires queue_at_n_orca(c, a, n)
    {
        queue_n(c, a, n).z
    }

    function sum_over_queue_i(c: Config, a: ActorAddr, i: Addr, incl: nat, excl: nat) : int
    //    ensures forall a: ActorAddr, i: Addr ::
    //            queue_at_n_orca(c, a, 0) ==>
    //            sum_over_queue_i(c, a, queue_at_n_orca_i(c, a, 0), 0) == queue_at_n_orca_z(c, a, 0)


    ////rcvORCA////
    predicate rcvORCA(c: Config, a: ActorAddr, c': Config)
    {
        queue_at_n_orca(c, a, 0) &&
        var i := queue_at_n_orca_i(c, a, 0);
        var z := queue_at_n_orca_z(c, a, 0);

        Owner(c, i, a) &&
        queue_at_n_orca(c, a, 0) &&
        actor_state_idle(c, a) &&
        pop(c, a, c') &&
        RC(c', i, a) == RC(c, i, a) + z &&
        (forall a' :: a' != a ==> unchanged_actor(c, a', c')) &&
        Ownership_Immutable(c, c')
    }

    predicate unchanged_actor(c: Config, a: ActorAddr, c': Config)

    lemma sum_over_orca_head_is_add_z(c: Config, i: Addr, a: ActorAddr)
        requires queue_at_n_orca(c, a, 0)
        ensures sum_over_queue_i(c, a, queue_at_n_orca_i(c, a, 0), 0, 1) == queue_at_n_orca_z(c, a, 0)

    lemma LRC_is_owner_RC(c: Config, i: Addr, a: ActorAddr)
        requires Owner(c, i, a)
        ensures LRC(c, i) == RC(c, i, a)

    lemma rcvORCA_changes_LRC(c: Config, a: ActorAddr, c': Config)
        requires rcvORCA(c, a, c')
        ensures forall n: nat, a', i ::
            a' != a ==>
            LRC(c', i) == LRC(c, i) &&
            n < queue_length(c', a') &&
            queue_length(c', a) == queue_length(c, a) ==>
            sum_over_queue_i(c', a', i, 0, n) == sum_over_queue_i(c, a, i, 0, n)

    predicate INV_6(c: Config) {
        forall i, a :: Owner(c, i, a) ==>
            (forall j: nat ::
                queue_at_n_orca(c, a, j) &&
                queue_at_n_orca_i(c, a, j) == i ==>
                LRC(c, i) > 0) &&
            (forall n: nat :: 
                0 < n <= queue_length(c, a) ==>
                    (forall j: nat ::
                        j >= n ==>
                            queue_at_n_orca(c, a, j) &&
                            queue_at_n_orca_i(c, a, j) == i ==>
                            orca_effect(c, a, i, 0, n) + orca_effect(c, a, i, n, queue_length(c,a)) > 0)) && 
            (forall n: nat ::
                n <= queue_length(c, a) ==>
                orca_effect(c, a, i, 0, n) >= 0)
    }

    function orca_effect(c: Config, a: ActorAddr, i: Addr, incl: nat, excl: nat) : int
    {
        LRC(c, i) + sum_over_queue_i(c, a, i, incl, excl)
    }

    lemma receive_orca_effect(c: Config, a: ActorAddr, c': Config, i: Addr, incl: nat, excl: nat) 
        requires rcvORCA(c, a, c') 
        requires incl>0
        requires excl>=incl
        ensures sum_over_queue_i(c', a, i, incl-1, excl-1) == sum_over_queue_i(c, a, i, incl, excl)

    lemma sum_over_queue_is_recursive(c: Config, a: ActorAddr, i: Addr, excl: nat)
        requires queue_at_n_orca(c, a, 0)
        requires queue_at_n_orca_i(c, a, 0) == i
        ensures sum_over_queue_i(c, a, i, 0, excl) == 
        sum_over_queue_i(c, a, i, 1, excl) + queue_at_n_orca_z(c, a, 0)
    
    lemma rcvORCA_preserves_INV_6(c: Config, a': ActorAddr, c': Config)
        requires INV_6(c)
        requires rcvORCA(c, a', c')
        ensures INV_6(c')
    {
        forall n: nat, j: nat, a, i |
            0 < n <= queue_length(c', a) &&
            j >= n &&
            queue_at_n_orca(c', a, j) &&
            queue_at_n_orca_i(c', a, j) == i 
            ensures orca_effect(c', a, i, 0, n) + orca_effect(c', a, i, n, queue_length(c', a)) > 0
        
        {
            if a == a' {
                var i_0 := queue_at_n_orca_i(c, a', 0);
                if i == i_0 {
                    assert queue_n(c', a', j) == queue_n(c, a', j+1);
                    assert queue_at_n_orca(c, a', j+1);
                    var z_0 := queue_at_n_orca_z(c, a', 0);
                    assert Owner(c, i, a');
                    assert RC(c', i_0, a') == RC(c, i_0, a') + z_0;
                    LRC_is_owner_RC(c, i_0, a');
                    LRC_is_owner_RC(c', i_0, a');

                    assert LRC(c', i_0) == LRC(c, i_0) + z_0;
                    assert orca_effect(c, a', i_0, 0, 1) >= 0;
                    assert LRC(c, i_0) + sum_over_queue_i(c, a', i_0, 0, 1) == orca_effect(c, a', i_0, 0, 1);
                    assert LRC(c, i_0) + sum_over_queue_i(c, a', i_0, 0, 1) >= 0;
                    sum_over_orca_head_is_add_z(c, i_0, a');
                    assert sum_over_queue_i(c, a', i_0, 0, 1) == z_0;
                    assert queue_at_n_orca(c, a, j+1);
                    assert queue_at_n_orca_i(c, a, j+1) == i;
                    //assert orca_effect(c', a, i, n) > 0;

                    /*
                    assert orca_effect(c, a, i, 0, n) + orca_effect(c, a, i, n, queue_length(c, a)) > 0;
                    sum_over_queue_is_recursive(c, a, i, n);
                    assert sum_over_queue_i(c, a, i, 0, n) == 
                        sum_over_queue_i(c, a, i, 1, n) + z_0;
                    receive_orca_effect(c, a, c', i, 1, n);
                    assert sum_over_queue_i(c', a, i, 0, n-1) == sum_over_queue_i(c, a, i, 1, n);
                    */
                    assert queue_length(c, a) == queue_length(c', a) + 1;
                    sum_over_queue_is_recursive(c, a, i, n+1);
                    assert sum_over_queue_i(c, a, i, 1, n+1) + z_0 == sum_over_queue_i(c, a, i, 0, n+1);
                    receive_orca_effect(c, a, c', i, 1, n+1);
                    assert sum_over_queue_i(c', a, i, 0, n) == sum_over_queue_i(c, a, i, 1, n+1);
                    assert orca_effect(c', a, i, 0, n) == orca_effect(c, a, i, 0, n+1);                   
                    
                            
                     

                    receive_orca_effect(c, a, c', i, n+1, queue_length(c, a));
                    assert orca_effect(c', a, i, n, queue_length(c, a) - 1) == orca_effect(c, a, i, n+1, queue_length(c, a));

                    assert orca_effect(c', a, i, 0, n) + orca_effect(c', a, i, n, queue_length(c, a) - 1) > 0;
                    assert orca_effect(c', a, i, 0, n) + orca_effect(c', a, i, n, queue_length(c', a)) > 0;
                     
                } else { assume false; }
            } else {
                assume false;
            }
        }
        

        forall i, a, n: nat |
                Owner(c', i, a) &&
                n <= queue_length(c', a)
                ensures LRC(c', i) + sum_over_queue_i(c', a, i, 0, n) >= 0
        {
            assume false;
        }
    }

    /*
    lemma rcvORCA_preserves_INV_6(c: Config, a': ActorAddr, c': Config)
        requires INV_6(c)
        requires rcvORCA(c, a', c')
        ensures INV_6(c')
    {
        rcvORCA_changes_LRC(c, a', c');
        sum_over_orca_head_is_add_z(c);
        sum_over_orca_head_is_add_z(c');
        forall n: nat, m: nat, i, a |
            Owner(c', i, a) &&
            queue_at_n_orca(c', a, n) &&
            queue_at_n_orca_i(c', a, n) == i &&
            m < queue_length(c', a)
            ensures LRC(c', i) > 0
            ensures LRC(c', i) + sum_over_queue_i(c', a, i, m) >= 0
         {
             if a' == a {
                assert true;
             } else {
                assert LRC(c', i) == LRC(c, i);
                assert LRC(c', i) > 0;
             }
            /*
            var z := queue_at_n_orca_z(c, a, 0);
            var i' := queue_at_n_orca_i(c', a, 0);
            assert LRC(c, i) + z == LRC(c, i) + sum_over_queue_i(c, a, i, 0);
            assert LRC(c, i) + z > 0;
            assert LRC(c', i) == LRC(c, i) + z;
            assert LRC(c', i) > 0;
            */
         }
    }
    */
    /*
    lemma rcvORCA_preserves_INV_2(c: Config, a: ActorAddr, c': Config)
        requires INV_2(c)
        requires rcvORCA(c, a, c')
        ensures INV_2(c')
    {

    } */

    predicate queue_head_orca(c: Config, a: ActorAddr)
    function queue_head_i(c: Config, a: ActorAddr) : Addr
    function queue_head_orca_z(c: Config, a: ActorAddr) : int



//    lemma rcvORCA_changes_RC(c: Config, a: ActorAddr, c': Config)
//        requires rcvORCA(c, a, c')


}

/* IGNORE
    //States//
    datatype State = idl | exe(f: Frame) | snd(f': Frame, a: Actor, m: Msg, ws: Workset)
                | mkU(ms: Marks) | trc(ms': Marks) | mkR(ms'': Marks) | cll(ms''': Marks)
    type Marks
    type Workset = set<Addr> //opaque - how?
    datatype RU = R | U
    function Marks_to_RU(m: Marks) : RU



    ////MESSAGES////
    datatype Msg = orca(i: Addr, z: int) | app(f: Frame) | ERR
    //datatype Frame = CFrame(b: BId, Map: map<VarId, Addr>) //opaque - how?
    datatype Frame = Frame(b: BId)
    function var_to_addr(f: Frame, v: VarId) : Addr


    ////IDs////
    type FId
    type BId
    type ClassId
    type VarId

    ////PATHS////
    datatype DP = This | LP(zero: int, x: VarId) | MP(k: int, x': VarId) | cons(dp: DP, f: FId)
    datatype SP = This | bsp(b: BId, x: VarId) | cons(sp: SP, f: FId)
    datatype Capability = WRITE | READ | TAG | ERR



    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : int
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int
    //{|(set x | exists a,k :: 0<=k<queue_length(c, a) && x==(a,k) && Reach(c,a,k,i))|}

    function Owner(c: Config, i: Addr) : ActorAddr
    function Field(c: Config, i: Addr, f: FId) : Addr //what do we need this for?
    function Class(c: Config, a: ActorAddr) : ClassId
    function Addrs(c: Config) : set<ActorAddr>

    predicate Reach(c: Config, a: ActorAddr, n: nat, i: Addr)

    ////DATA-RACE FREEDOM////
    function sees(cid: ClassId, sp: SP) : Capability
    function views(c: Config, a: ActorAddr, p:DP) : Capability

    lemma {:verify true} A1(a: Actor, sp: SP, f: FId, cappa: Capability)
    requires sees(a.cl, SP.cons(sp, f)) == cappa //pass cappa as param instead?
    ensures exists cappa' :: cappa' != TAG && sees(a.cl, sp) == cappa'


    lemma {:verify true} A2(a: Actor, sp: SP, f: FId)
    requires sees(a.cl, SP.cons(sp, f)) == WRITE
    ensures sees(a.cl, sp) == WRITE

    function C(c: Config, a: ActorAddr, dp: DP) : Addr
    function A(c: Config, a: ActorAddr, dp: DP) : (Addr, Capability)
   /*
     predicate WF_A(c: Config, a: ActorAddr, dp: DP) {
        forall i: Addr :: ((exists k: Capability ::
        A(c,a,dp) == (i, k)) <==> (C(c,a,dp) == i && views(c,a,dp) == k
                                || k == TAG && exists k', i', p' ::
                                (p == Cons(p',) && A(c,a,p') == (i', k') && Owner(c, i') == i)))

    }
    */
    /*
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr :: (a != a' && (exists k :: A(c, a, p) == (i, k) && k==WRITE)
                                            ==> (exists k' :: A(c, a', p') == (i, k') ==> k' == TAG))
    } */
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr :: (a != a' && (exists k :: A(c, a, p) == (i, k) && k==WRITE)
                                            && exists k' :: A(c, a', p') == (i, k') ==> k' == TAG)
    }

    ////AUXILIARY FUNCTION////
    //TODO: separate into its own module
    function queue_length(c: Config, a: ActorAddr) : int {
        Actors(a,c).q.length

    }
}
