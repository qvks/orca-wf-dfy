/* 
 * AUTOMATED PROOF OF ORCA INVARIANT PRESERVATION
 * ATOMIC STATE TRANSITIONS
 * OPAQUE DATATYPES
 * one file due to Dafny's module specifics 
 */

/*
 * Variable naming convention 
 * in agreement with the paper's current formalism :
 * a: ActorAddr
 * iota: Addr
 * c: Config (current)
 * c': Config (after transition)
 * st: State
 * lp: Local path 
 * mp: message path 
 * dp: dynamic path 
 * sp: static path 
 */

abstract module Opaque{
    ////CONFIG////
    type Config
    type Actor
    type Frame
    //old app constructor app(is, b) left in for backwards compatibility 
    //with earlier versions of the paper
    datatype Msg = orca(iota: Addr, z: int) | app(is: set<Addr>, b: BId) | app'(f: Frame)| ERR
    function Heap(c: Config, iota: Addr, fid: FId) : Addr
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
    //dynamic path (local path or message path)
    type DP
    //static path 
    type SP

    ////ACTORS////
    //all valid actor addresses are in the domain of Actors
    function Actors(c: Config, a: ActorAddr) : Actor

    ////REFERENCE COUNTS////
    function RC(c: Config, iota: Addr, a: ActorAddr) : nat
    //Orca Message Count
    function OMC(c: Config, iota: Addr) : int
    //Application Message Count
    function AMC(c: Config, iota: Addr) : int
    //Locar Referece Count
    function LRC(c: Config, iota: Addr) : int
    //Foreign Reference Count
    function FRC(c: Config, iota: Addr) : int
    
    lemma LRC_is_owner_RC(c: Config, iota: Addr, a: ActorAddr)
        requires Owner(c, iota, a)
        ensures LRC(c, iota) == RC(c, iota, a)
    
    lemma FRC_is_not_owner_RC(c: Config, iota: Addr, actors: set<ActorAddr>) 
        requires forall a ::    
                    a in actors <==>
                    !Owner(c, iota, a) 
        ensures FRC(c, iota) == sum_over_set_RC(c, actors)

    function sum_over_set_RC(c: Config, actors: set<ActorAddr>) : nat
    /////////////////////////


    /////DATA RACE FREEDOM/////
    predicate DRF(c: Config) {
        forall a, a': ActorAddr, p, p': DP, iota: Addr, k: Capability ::
            a != a' &&
            A(c, a, p, iota, WRITE) &&
            A(c, a', p', iota, k) ==>
            k == TAG
    }
    /////////////////////////


    //////ACCESSIBILITY/REACHABILITY////// 

    //An actor can reach an object if there is a path from 
    //the actor to the object 
    predicate Reachable(c: Config, iota: Addr, a: ActorAddr, f: Frame)

    //An actor can access an object if there is a LEGAL path from 
    //the actor to the object 
    predicate A(c: Config, a: ActorAddr, dp: DP, iota: Addr, k: Capability)

    predicate accessible_via_lp(c: Config, iota: Addr, a: ActorAddr) {
        exists lp,k ::
            A(c, a, lp, iota, k)
    }

    predicate is_a_message_path(c: Config, mp: DP)

    predicate live(c: Config, a: ActorAddr, iota: Addr) {
        exists k, dp ::
            A(c, a, dp, iota, k)
    }

    predicate msg_live(c: Config, a: ActorAddr, iota: Addr, n: nat) {
        (exists k, mp ::
            A(c, a, mp, iota, k) &&
            is_a_message_path(c, mp) &&
            message_path_from_n(c, mp, n)) ||
        (queue_at_n_orca(c, a, n) &&
        queue_at_n_orca_i(c, a, n) == iota)
    }
    
    //message path mp from n'th message in a queue
    predicate message_path_from_n(c: Config, mp: DP, n: nat)

    function all_reachable(c: Config, a: ActorAddr, f: Frame) : set<Addr>
    /////////////////////////


    //////////////////////////////INVARIANTS///////////////////////////////

    predicate INV_1() {
        forall c ::
            DRF(c)
    }

    predicate INV_2(c: Config) {
        forall iota, dp, mp, k, a, a_own ::
            (A(c, a, dp, iota, k) &&
            !Owner(c, iota, a)) ||
            (A(c, a_own, mp, iota, k) &&
            Owner(c, iota, a_own) &&
            is_a_message_path(c, mp)) ==>
            LRC(c, iota) > 0
    }

    predicate INV_3(c: Config) {
        forall iota, dp, k, a ::
            A(c, a, dp, iota, k) &&
            !Owner(c, iota, a) ==>
            RC(c, iota, a) > 0
    }

    predicate INV_4(c: Config) {
        forall iota ::
            LRC(c, iota) + OMC(c, iota) == FRC(c, iota) + AMC(c, iota)
    }

    predicate INV_5(c: Config) 
    //RC returns a nat. Therefore, INV_5 holds implicitly

    predicate INV_6(c: Config) {
        forall iota, a :: Owner(c, iota, a) ==>

            (forall n: nat ::
                n <= queue_length(c, a) ==>
                LRC_plus_queue_effect(c, a, iota, n) >= 0) &&

            (forall a' ::
                a != a' &&
                live(c, a', iota) ==>
                forall j: nat ::
                    j <= queue_length(c, a) ==>
                    LRC_plus_queue_effect(c, a, iota, j) > 0) &&

            (forall n: nat ::
                n < queue_length(c, a) &&
                msg_live(c, a, iota, n) ==>
                forall j: nat ::
                    j <= n ==>
                    LRC_plus_queue_effect(c, a, iota, j) > 0)
    }
    ///////////////////////////////////////////////////////////////////////////


    /////SYSTEM PROPERTIES/////
    predicate Ownership_Immutable(c: Config, c': Config)
    {
        forall iota, a' :: 
            Owner(c, iota, a') == Owner(c', iota, a')
    }

    lemma Ownership_Unique(c: Config)
        ensures forall iota, a, a' ::
            Owner(c, iota, a) &&
            a != a' ==>
            !Owner(c, iota, a')
    ///////////////////////////


    ///////////////PSEUDO CODE FOR RECEIVING MESSAGES (FIGURE 6)///////////////

    ////RcvApp////
    predicate RcvApp(c: Config, a: ActorAddr, c': Config)
        requires actor_state_idle(c, a)
        requires queue_at_n_app(c, a, 0)
    {
        actor_state_rcv(c', a) &&
        actor_ws(c', a) == set iota |
            iota in allocated_addresses(c) &&
            exists mp,k ::
            mp in paths_from_message_n(c, a, 0) &&
            A(c,a,mp,iota,k)
    }

    ////RcvToExe////
    predicate RcvToExe(c: Config, a: ActorAddr, c': Config)
    {
        actor_state_rcv(c, a) &&
        queue_at_n_app(c, a, 0) &&
        actor_state_exe(c', a) &&
        actor_state_exe_f(c', a) == frame_from_app_message_n(c, a, 0) &&
        pop(c, a, c') &&
        Ownership_Immutable(c, c') &&

        (forall iota :: 
            iota in actor_ws(c, a) && 
            Owner(c, iota, a) ==> 
            RC(c', iota, a) == RC(c, iota, a) - 1) &&

        (forall iota :: 
            iota in actor_ws(c, a) && 
            !Owner(c, iota, a) ==> 
            RC(c', iota, a) == RC(c, iota, a) + 1) &&

        (forall iota :: 
            iota !in actor_ws(c, a) ==> 
            RC(c', iota, a) == RC(c, iota, a)) &&

        (forall iota, a' :: 
            a' != a ==> 
            RC(c', iota, a') == RC(c, iota, a'))
    }


    lemma RcvToExe_Increases_A(c: Config, a: ActorAddr, c': Config)
        requires RcvToExe(c, a, c')
        ensures forall lp, iota, k :: 
            A(c, a, lp, iota, k) ==> 
            A(c', a, lp, iota, k)

        ensures forall lp, iota, k :: 
            A(c', a, lp, iota, k) ==> 
            A(c, a, lp, iota, k) || 
            iota in actor_ws(c, a)

        ensures forall lp, iota, k, a' :: 
            a' != a ==> 
            A(c', a', lp, iota, k) == A(c, a', lp, iota, k)


    lemma RcvToExe_Preserves_INV_3(c: Config, a': ActorAddr, c': Config)
        requires INV_3(c)
        requires RcvToExe(c, a', c')
        ensures INV_3(c')
    {
        RcvToExe_Increases_A(c, a', c');
        forall iota, lp, k, a |
            A(c', a, lp, iota, k) &&
            !Owner(c', iota ,a)
            ensures RC(c', iota, a) > 0
        {
            if a' == a && iota in actor_ws(c, a) {
                assert RC(c, iota, a) >= 0;
                assert RC(c', iota, a) == RC(c, iota, a) + 1;
            } else {
                assert RC(c', iota, a) == RC(c, iota, a);
                assert RC(c, iota, a) > 0;
                assert RC(c', iota, a) > 0;
            }
        }
    }

    ////AUXILIARY FOR RcvApp////
    predicate actor_state_idle(c: Config, a: ActorAddr)

    predicate actor_state_rcv(c: Config, a: ActorAddr)

    function paths_from_message_n(c: Config, a: ActorAddr, n: nat) : set<DP>
        requires n < queue_length(c, a)

    function actor_ws(c: Config, a: ActorAddr) : set<Addr>
        requires actor_state_rcv(c, a) || actor_state_snd(c, a)
    
    //a is iota's owner in c
    predicate Owner(c: Config, iota: Addr, a: ActorAddr)

    predicate actor_state_exe(c: Config, a: ActorAddr)

    function frame_from_app_message_n(c: Config, a: ActorAddr, n: nat) : Frame
    ///////////////////////////

    ///////////////PSEUDO CODE FOR RECEIVING AN ORCA MESSAGE (FIGURE 7)///////////////

    ////rcvORCA////
    predicate rcvORCA(c: Config, a: ActorAddr, c': Config)
    {
        queue_at_n_orca(c, a, 0) &&
        var iota := queue_at_n_orca_i(c, a, 0);
        var z := queue_at_n_orca_z(c, a, 0);

        Owner(c, iota, a) &&
        queue_at_n_orca(c, a, 0) &&
        actor_state_idle(c, a) &&
        pop(c, a, c') &&
        RC(c', iota, a) == RC(c, iota, a) + z &&
        Ownership_Immutable(c, c') &&

        (forall a' :: 
            a' != a ==>
            unchanged_actor(c, a', c')) 
    }

    ////AUXILIARY FOR rcvORCA////
    lemma sum_over_orca_head_is_add_z(c: Config, iota: Addr, a: ActorAddr)
        requires queue_at_n_orca(c, a, 0)
        ensures queue_effect(c, a, queue_at_n_orca_i(c, a, 0), 0, 1) == queue_at_n_orca_z(c, a, 0)
    
    function queue_effect(c: Config, a: ActorAddr, iota: Addr, incl: nat, excl: nat) : int

    function LRC_plus_queue_effect(c: Config, a: ActorAddr, iota: Addr, excl: nat) : int
    {
        LRC(c, iota) + queue_effect(c, a, iota, 0, excl)
    }

    lemma queue_effect_pop(c: Config, a: ActorAddr, c': Config, iota: Addr, incl: nat, excl: nat)
        requires rcvORCA(c, a, c')
        requires incl>0
        requires excl>=incl
        ensures queue_effect(c', a, iota, incl-1, excl-1) == queue_effect(c, a, iota, incl, excl)

    lemma msg_live_pop(c: Config, a: ActorAddr, c': Config, iota: Addr, n: nat)
        requires rcvORCA(c, a, c')
        requires msg_live(c', a, iota, n)
        ensures msg_live(c, a, iota, n+1)

    lemma LRC_plus_queue_effect_shift(c: Config, a: ActorAddr, c': Config, iota: Addr, k: nat)
        requires rcvORCA(c, a, c')
        ensures LRC_plus_queue_effect(c, a, iota, k+1) == LRC_plus_queue_effect(c', a, iota, k)
        ensures forall a', iota' ::
            a' != a &&
            Owner(c, iota', a') ==>
            LRC_plus_queue_effect(c, a', iota', k) == LRC_plus_queue_effect(c', a', iota', k)

    lemma rcvORCA_accessibility_unaffected(c: Config, a: ActorAddr, iota: Addr, c': Config)
        requires rcvORCA(c, a, c')
        requires queue_at_n_orca_i(c, a, 0) == iota
        ensures forall a', iota ::
            a' != a ==>
            (live(c, a', iota) <==>
            live(c', a', iota))
        ensures forall a, iota' ::
            iota != iota' ==>
            (live(c, a, iota') <==>
            live(c', a, iota'))
    //////////////////////////////

    lemma rcvORCA_preserves_INV_6(c: Config, a_own: ActorAddr, c': Config)
        requires INV_6(c)
        requires INV_2(c)
        requires rcvORCA(c, a_own, c')
        ensures INV_6(c')
    {
        //INV_6.[b]
        forall a, iota, j: nat |
                Owner(c', iota, a) &&
                j <= queue_length(c', a)
                ensures LRC_plus_queue_effect(c', a, iota, j) >= 0
        {
            if a == a_own {
                var i_0 := queue_at_n_orca_i(c, a, 0);
                if iota == i_0 {
                    LRC_plus_queue_effect_shift(c, a, c', iota, j);
                } else {
                    LRC_plus_queue_effect_shift(c, a, c', iota, j);
                }
            } else {
                LRC_plus_queue_effect_shift(c, a_own, c', iota, j);
                assert unchanged_actor(c, a, c');
            }
        }

        //INV_6.[c]
        forall a, a', iota, j: nat |
            Owner(c', iota, a) &&
            a != a' &&
            live(c', a', iota) &&
            j <= queue_length(c', a)
            ensures LRC_plus_queue_effect(c', a, iota, j) > 0
        {
            var i_0 := queue_at_n_orca_i(c, a_own, 0);
            if a == a_own {
                rcvORCA_accessibility_unaffected(c, a_own, i_0, c');
                LRC_plus_queue_effect_shift(c, a, c', iota, j);
            } else {
                Ownership_Unique(c');
                rcvORCA_accessibility_unaffected(c, a_own, i_0, c');
                assert unchanged_actor(c, a, c');
                LRC_plus_queue_effect_shift(c, a_own, c', iota, j);
            }
        }

        //INV_6.[a]
        forall a, iota, j: nat, n: nat |
            Owner(c', iota, a) &&
            n < queue_length(c', a) &&
            msg_live(c', a, iota, n) &&
            j <= n
            ensures LRC_plus_queue_effect(c', a, iota, j) > 0
        {
            var i_0 := queue_at_n_orca_i(c, a_own, 0);
            if a == a_own {
                LRC_plus_queue_effect_shift(c, a, c', iota, j);
                msg_live_pop(c, a, c', iota, n);
            } else {
                LRC_plus_queue_effect_shift(c, a_own, c', iota, j);
                assert unchanged_actor(c, a, c');
            }
        }
    }

    ///////////////PSEUDO CODE FOR SENDING MESSAGES (FIGURE 8)///////////////

    ////ExeToSnd////
    predicate ExeToSnd(c: Config, a: ActorAddr, a': ActorAddr, c': Config, c'': Config, msg: Msg) 
        requires actor_state_exe(c, a)
        requires queue_at_n_app(c'', a', queue_length(c, a'))
        requires push(c, a', msg, c'') 
        requires msg.app?
        requires subset(frame_rng(msg_f(c, msg)), frame_rng(actor_state_exe_f(c, a)))
        requires disjoint(frame_dom(msg_f(c, msg)), frame_dom(actor_state_exe_f(c, a)))
        requires DRF(c'')
        
    {
        actor_state_snd(c', a) &&
        actor_state_snd_a'(c', a) == a' &&
        actor_state_snd_f'(c', a) == queue_at_n_app_f(c'', a', queue_length(c, a')) &&
        actor_state_snd_f(c', a) == actor_state_exe_f(c, a) &&
        actor_ws(c', a) == {} &&
        all_else_unmodified(c, a, c')
    }

    ////SndToExe////
    predicate SndToExe(c: Config, a: ActorAddr, a': ActorAddr, c': Config, c'': Config) 
    {
        actor_state_snd(c, a) &&
        actor_state_snd_a'(c, a) == a' &&

        all_else_unmodified(c, a, c') &&
        Ownership_Immutable(c, c') &&

        var f := actor_state_snd_f(c, a);
        var f' := actor_state_snd_f'(c, a);
        var ws := actor_ws(c, a);
        
        (forall iota :: 
            iota in ws && 
            Owner(c, iota, a) ==> 
            RC(c', iota, a) == RC(c, iota, a) + 1 &&
            FRC(c', iota) == FRC(c, iota) &&
            OMC(c', iota) == OMC(c, iota) &&
            LRC(c', iota) == LRC(c, iota) + 1) &&

        (forall iota :: 
            iota in ws &&
            !Owner(c, iota, a) &&
            RC(c, iota, a) > 1 ==>
            RC(c', iota, a) == RC(c, iota, a) - 1 &&
            OMC(c', iota) == OMC(c, iota) &&
            LRC(c', iota) == LRC(c, iota) &&
            FRC(c', iota) == FRC(c, iota) - 1) &&
    
        (forall iota :: 
            iota in ws &&
            !Owner(c, iota, a) &&
            RC(c, iota, a) == 1 ==>
            RC(c', iota, a) == RC(c, iota, a) + 255 &&
            OMC(c', iota) == OMC(c, iota) + 256 &&
            LRC(c', iota) == LRC(c, iota) &&
            FRC(c', iota) == FRC(c, iota) + 255) &&

        actor_state_exe(c', a) &&
        actor_state_exe_f(c', a) == f &&

        (forall iota ::
            iota in ws ==>
            AMC(c', iota) == AMC(c, iota) + 1)
    }

    lemma SndToExe_preserves_INV_4(c: Config, a: ActorAddr, a': ActorAddr, c': Config, c'': Config)
        requires INV_4(c)
        requires SndToExe(c, a, a', c', c'')
        requires ws_WF(c, a, actor_state_snd_f(c, a), actor_state_snd_f'(c, a))
        ensures INV_4(c') 
    {
        forall iota |
        true 
        ensures LRC(c', iota) + OMC(c', iota) == FRC(c', iota) + AMC(c', iota) 
        {   
        }
    }
        
    /////////Auxiliary for ExeToSnd and SndToExe////////// 
    // generalise into fewer methods when the paper's formalism
    // is firmly decided on    

    predicate actor_state_snd(c: Config, a: ActorAddr)

    function actor_state_snd_msg(c: Config, a: ActorAddr) : Msg 
        requires actor_state_snd(c, a)

    function actor_state_snd_f'(c: Config, a: ActorAddr) : Frame
        requires actor_state_snd(c, a)

    function actor_state_snd_a'(c: Config, a: ActorAddr) : ActorAddr
        requires actor_state_snd(c, a)
     
    function msg_f(c: Config, msg: Msg) : Frame

    function actor_state_snd_f(c: Config, a: ActorAddr) : Frame 
        requires actor_state_snd(c, a)

    function actor_state_exe_f(c: Config, a: ActorAddr) : Frame 
        requires actor_state_exe(c, a)

    function queue_at_n_app_f(c: Config, a: ActorAddr, n: nat) : Frame
        requires queue_at_n_app(c, a, n)

    function frame_dom(f: Frame) : set<VarId>

    function frame_rng(f: Frame) : set<Addr>

    predicate ws_WF(c: Config, a: ActorAddr, f: Frame, f': Frame)
        requires actor_state_snd(c, a)
    {
        var ws := actor_ws(c, a);

        (forall iota ::
            Reachable(c, iota, a, f) ==>
            (iota in actor_ws(c, a) ||
            exists iota' ::
                iota' in ws &&
                subset(frame_rng(f'), ws) &&
                subset(ws, all_reachable(c, a, f')))) &&

        (forall iota ::
            iota in ws ==>
            RC(c, iota, a) >= 1)
    }

    
    predicate all_else_unmodified(c: Config, modified: ActorAddr, c': Config) 
    {
        (forall a ::
            !actor_state_snd(c, modified) &&
            a != modified ==>
            unchanged_actor(c, a, c')) &&

        (forall a ::
            actor_state_snd(c, modified) &&
            a != modified &&
            a != actor_state_snd_a'(c, modified) ==>
            unchanged_actor(c, a, c')) &&

        (actor_state_snd(c, modified) ||
        actor_state_rcv(c, modified) ==>
        forall iota :: 
            iota !in actor_ws(c, modified) ==>
            unchanged_object(c, iota, c'))
    }

    predicate unchanged_object(c: Config, iota: Addr, c': Config)
    {
         OMC(c, iota) == OMC(c', iota) && 
         LRC(c, iota) == LRC(c', iota) &&
         FRC(c, iota) == FRC(c', iota) &&
         AMC(c, iota) == AMC(c', iota)
    }

    predicate unchanged_actor(c: Config, a: ActorAddr, c': Config)
    {
        queue_length(c, a) == queue_length(c', a) &&
        (forall iota, n: nat ::
            msg_live(c, a, iota, n) <==> 
            msg_live(c', a, iota, n)) &&
        
        (forall iota ::
            RC(c, iota, a) == RC(c', iota, a))
    }
    ////////////////////////////////////////////////////// 

    ////////////////////OPAQUE ADTs/////////////////////

    ///////////SETS///////////
    predicate subset(Set: set<Addr>, subset: set<Addr>) {
        forall iota ::  
            iota in subset ==>
            iota in Set
    }

    predicate disjoint(Set: set<VarId>, Set': set<VarId>) {
        forall iota ::  
            iota in Set ==>
            iota !in Set'
    }
    
    function union(Set: set<Addr>, Set': set<Addr>) : set<Addr>
    ensures forall iota ::
            (iota in Set || 
            iota in Set') ==>
            iota in union(Set, Set')
    /////////////////////////

    /////////QUEUES/////////
    function queue_length(c: Config, a: ActorAddr) : nat

    //nth message in the queue
    function queue_n(c: Config, a: ActorAddr, n: nat) : Msg

    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then queue_n(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue(c: Config, a: ActorAddr) {
        (forall n: nat :: 
            n < queue_length(c,a) ==> 
            queue_n(c, a, n) != Msg.ERR) &&

        (forall n: nat :: 
            n >= queue_length(c,a) ==> 
            queue_n(c,a,n) == Msg.ERR)
    }

    predicate push(c: Config, a: ActorAddr, msg: Msg, c': Config)
    {
        WF_queue(c, a) &&
        msg != Msg.ERR &&
        queue_length(c', a) == queue_length(c, a) + 1 &&
        queue_n(c', a, queue_length(c,a)) == msg &&

        (forall n: nat :: 
            n != queue_length(c,a) ==>
            queue_n(c', a, n) == queue_n(c, a, n))
    }

    lemma push_preserves_WF_queue(c: Config, a: ActorAddr, msg: Msg, c': Config)
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

    lemma pop_preserves_WF_queue(c: Config, a: ActorAddr, c': Config)
        requires pop(c, a, c')
        ensures WF_queue(c', a)
    {
    }

    //ORCA MESSAGES IN QUEUE//
    predicate queue_at_n_orca(c: Config, a: ActorAddr, n: nat)
        ensures queue_at_n_orca(c, a, n) ==> n <= queue_length(c, a)
    {
        WF_queue(c, a) &&
        queue_n(c, a, n).orca?
    }

    function queue_at_n_orca_i(c: Config, a: ActorAddr, n: nat) : Addr
        requires queue_at_n_orca(c, a, n)
    {
        queue_n(c, a, n).iota
    }

    function queue_at_n_orca_z(c: Config, a: ActorAddr, n: nat) : int
        requires queue_at_n_orca(c, a, n)
    {
        queue_n(c, a, n).z
    }
    
    //APP MESSAGES IN QUEUE//
    predicate queue_at_n_app(c: Config, a: ActorAddr, n: nat)
        ensures queue_at_n_app(c, a, n) ==> n <= queue_length(c, a)
    {
        WF_queue(c, a) &&
        queue_n(c, a, n).app?
    }

    function queue_at_n_app_is(c: Config, a: ActorAddr, n: nat) : set<Addr>
        requires queue_at_n_app(c, a, n)
    {
        queue_n(c, a, n).is
    }
    
    function queue_at_n_app_b(c: Config, a: ActorAddr, n: nat) : BId
        requires queue_at_n_app(c, a, n)
    {
        queue_n(c, a, n).b
    }
    /////////////////////////
    ////////////////////////////////////////////////////// 

}


