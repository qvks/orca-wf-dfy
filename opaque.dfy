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

        (forall n: nat :: 
            n >= 0 ==>
            queue_n(c', a, n) == queue_n(c, a, n+1)) 
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


    ////DATA RACE FREEDOM////
    predicate DRF(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr, k: Capability::
            a != a' &&
            A(c, a, p, i, WRITE) &&
            A(c, a', p', i, k) ==>
            k == TAG
    }

    predicate is_a_message_path(c: Config, mp: DP)

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

    predicate INV_3(c: Config) {
        forall i, dp, k, a ::
            A(c, a, dp, i, k) &&
            !Owner(c, i, a) ==>
            RC(c, i, a) > 0
    }


    predicate INV_6(c: Config) {
        forall i, a :: Owner(c, i, a) ==>
            
            (forall n: nat ::
                n <= queue_length(c, a) ==>
                LRC_plus_queue_effect(c, a, i, n) >= 0) &&

            (forall a' :: 
                a != a' && 
                live(c, a', i) ==>
                forall j: nat ::
                    j <= queue_length(c, a) ==>
                    LRC_plus_queue_effect(c, a, i, j) > 0) &&

            (forall n: nat ::
                n < queue_length(c, a) && 
                msg_live(c, a, i, n) ==>
                forall j: nat ::
                    j <= n ==>
                    LRC_plus_queue_effect(c, a, i, j) > 0)
    }

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

    function queue_effect(c: Config, a: ActorAddr, i: Addr, incl: nat, excl: nat) : int

    predicate A(c: Config, a: ActorAddr, dp: DP, i: Addr, k: Capability)
        
    predicate live(c: Config, a: ActorAddr, i: Addr) {
        exists k, dp ::
            A(c, a, dp, i, k)    
    }
        
    predicate msg_live(c: Config, a: ActorAddr, i: Addr, n: nat) {
        (exists k, mp ::
            A(c, a, mp, i, k) && 
            is_a_message_path(c, mp) &&
            message_path_from_n(c, mp, n)) ||
        (queue_at_n_orca(c, a, n) &&
        queue_at_n_orca_i(c, a, n) == i)
    }
        
    predicate message_path_from_n(c: Config, mp: DP, n: nat)

    //////////////////////////

    /////SYSTEM PROPERTIES/////
    predicate Ownership_Immutable(c: Config, c': Config)
    {
        forall i, a' :: Owner(c, i, a') == Owner(c', i, a')
    }

    lemma Ownership_Unique(c: Config)
        ensures forall i, a, a' :: 
            Owner(c, i, a) &&
            a != a' ==> 
            !Owner(c, i, a')
    ///////////////////////////

    ///////////////PSEUDO CODE FOR RECEIVING MESSAGES (FIGURE 6)///////////////

    ////RcvApp////
    predicate RcvApp(c: Config, a: ActorAddr, c': Config)
        requires actor_state_idle(c, a)
        requires queue_at_n_app(c, a, 0)
    {
        actor_state_rcv(c', a) &&
        actor_ws(c', a) == set i |
            i in allocated_addresses(c) &&
            exists mp,k ::
            mp in paths_from_message_n(c, a, 0) &&
            A(c,a,mp,i,k)
    }

    ////RcvToExe//// 
    predicate RcvToExe(c: Config, a: ActorAddr, c': Config)
    {
        actor_state_rcv(c, a) &&
        queue_at_n_app(c, a, 0) &&
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

    predicate queue_at_n_app(c: Config, a: ActorAddr, n: nat)
        ensures queue_at_n_app(c, a, n) ==> n <= queue_length(c, a)
    {
        WF_queue(c, a) &&
        queue_n(c, a, n).app?
    }

    predicate actor_state_rcv(c: Config, a: ActorAddr)

    function paths_from_message_n(c: Config, a: ActorAddr, n: nat) : set<DP>
        requires n < queue_length(c, a)

    function actor_ws(c: Config, a: ActorAddr) : set<Addr>
        requires actor_state_rcv(c, a)

    function queue_at_n_app_is(c: Config, a: ActorAddr, n: nat) : set<Addr>
        requires queue_at_n_app(c, a, n)
        
    predicate Owner(c: Config, i: Addr, a: ActorAddr)

    predicate actor_state_exe(c: Config, a: ActorAddr)

    function actor_state_exe_frame(c: Config, a: ActorAddr) : Frame

    function frame_from_app_message_n(c: Config, a: ActorAddr, n: nat) : Frame
    ///////////////////////////

    ///////////////PSEUDO CODE FOR RECEIVING AN ORCA MESSAGE (FIGURE 7)///////////////

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
        // SD: what is state of actor a in c'? And what about the contents of actor's fields?
    }

    ////AUXILIARY FOR rcvORCA////
    predicate unchanged_actor(c: Config, a: ActorAddr, c': Config) 
    {
        queue_length(c, a) == queue_length(c', a) &&
        forall i, n: nat :: msg_live(c, a, i, n) <==> msg_live(c', a, i, n)
    }

    lemma sum_over_orca_head_is_add_z(c: Config, i: Addr, a: ActorAddr)
        requires queue_at_n_orca(c, a, 0)
        ensures queue_effect(c, a, queue_at_n_orca_i(c, a, 0), 0, 1) == queue_at_n_orca_z(c, a, 0)

    lemma LRC_is_owner_RC(c: Config, i: Addr, a: ActorAddr)
        requires Owner(c, i, a)
        ensures LRC(c, i) == RC(c, i, a)


    function LRC_plus_queue_effect(c: Config, a: ActorAddr, i: Addr, excl: nat) : int
    {
        LRC(c, i) + queue_effect(c, a, i, 0, excl)
    }

    lemma queue_effect_pop(c: Config, a: ActorAddr, c': Config, i: Addr, incl: nat, excl: nat)
        requires rcvORCA(c, a, c')
        requires incl>0
        requires excl>=incl
        ensures queue_effect(c', a, i, incl-1, excl-1) == queue_effect(c, a, i, incl, excl)

    lemma msg_live_pop(c: Config, a: ActorAddr, c': Config, i: Addr, n: nat)
        requires rcvORCA(c, a, c')
        requires msg_live(c', a, i, n)
        ensures msg_live(c, a, i, n+1)
 
    lemma LRC_plus_queue_effect_shift(c: Config, a: ActorAddr, c': Config, i: Addr, k: nat)
        requires rcvORCA(c, a, c')
        ensures LRC_plus_queue_effect(c, a, i, k+1) == LRC_plus_queue_effect(c', a, i, k)
        ensures forall a', i' :: a' != a && Owner(c, i', a') ==> 
                LRC_plus_queue_effect(c, a', i', k) == LRC_plus_queue_effect(c', a', i', k)

    lemma rcvORCA_accessibility_unaffected(c: Config, a: ActorAddr, i: Addr, c': Config)
        requires rcvORCA(c, a, c')
        requires queue_at_n_orca_i(c, a, 0) == i
        ensures forall a', i :: 
            a' != a ==>
            (live(c, a', i) <==> 
            live(c', a', i))
        ensures forall a, i' ::
            i != i' ==>
            (live(c, a, i') <==>
            live(c', a, i'))
    
    //////////////////////////////

    lemma rcvORCA_preserves_INV_6(c: Config, a_own: ActorAddr, c': Config)
        requires INV_6(c)
        requires INV_2(c)
        requires rcvORCA(c, a_own, c')
        ensures INV_6(c')
    {
        forall a, i, j: nat | 
                Owner(c', i, a) &&
                j <= queue_length(c', a) 
                ensures LRC_plus_queue_effect(c', a, i, j) >= 0
        {
            if a == a_own {
                var i_0 := queue_at_n_orca_i(c, a, 0);
                if i == i_0 {
                    LRC_plus_queue_effect_shift(c, a, c', i, j);
                } else {
                    LRC_plus_queue_effect_shift(c, a, c', i, j);
                }
            } else {
                LRC_plus_queue_effect_shift(c, a_own, c', i, j);
                assert unchanged_actor(c, a, c'); 
            }
        } 

        forall a, a', i, j: nat |
            Owner(c', i, a) &&
            a != a' && 
            live(c', a', i) &&
            j <= queue_length(c', a) 
            ensures LRC_plus_queue_effect(c', a, i, j) > 0
        {
            var i_0 := queue_at_n_orca_i(c, a_own, 0);
            if a == a_own {
                rcvORCA_accessibility_unaffected(c, a_own, i_0, c');
                LRC_plus_queue_effect_shift(c, a, c', i, j);
            } else {
                Ownership_Unique(c');
                rcvORCA_accessibility_unaffected(c, a_own, i_0, c');
                assert unchanged_actor(c, a, c'); 
                LRC_plus_queue_effect_shift(c, a_own, c', i, j);
            }
        }

        forall a, i, j: nat, n: nat |
            Owner(c', i, a) &&
            n < queue_length(c', a) && 
            msg_live(c', a, i, n) &&
            j <= n 
            ensures LRC_plus_queue_effect(c', a, i, j) > 0
        {
            var i_0 := queue_at_n_orca_i(c, a_own, 0);
            if a == a_own {
                LRC_plus_queue_effect_shift(c, a, c', i, j);
                msg_live_pop(c, a, c', i, n);
            } else {
                LRC_plus_queue_effect_shift(c, a_own, c', i, j);
                assert unchanged_actor(c, a, c'); 
            }
        }
    }
}
        

