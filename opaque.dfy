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
    type FId 
    function Heap(c: Config, i: Addr, fid: FId) : Addr 
    

    ////ADDRESSES////
    datatype Addr = OA(ObjectAddr) | AA(ActorAddr) | Null
    type ObjectAddr 
    type ActorAddr
    

    ////ACTORS////
//    datatype Actor = Actor(st: State, cl: ClassId)
    //lemma RANGE OF ACTORS IS FINITE
    //lemma all valid actor addresses are in the domain of Actors
    function Actors(c: Config, a: ActorAddr) : Actor

    //Queues//
    //length added to convince Dafny that queues are finite 
    //Is there a better way?
    //datatype Queue = Queue(msg: Msg, length: int) //opaque - how?
    function queue_length(c: Config, a: ActorAddr) : nat 
    function queue_n(c: Config, a: ActorAddr, n: nat) : Msg 

    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then queue_n(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue(c: Config, a: ActorAddr) {
        (forall n:nat :: n < queue_length(c,a) ==> queue_n(c, a, n) != Msg.ERR) &&
        (forall n:nat :: n >= queue_length(c,a) ==> queue_n(c,a,n) == Msg.ERR)
    }

    predicate push(c: Config, a: ActorAddr, msg: Msg, c': Config)
    {
        WF_queue(c,a) && msg != Msg.ERR &&
        queue_length(c', a) == queue_length(c, a) + 1 && queue_n(c', a, queue_length(c,a)) == msg &&
        forall n:nat :: n != queue_length(c,a) ==> queue_n(c',a,n) == queue_n(c,a,n) 
    }

    lemma push_preserves_WF_queue(c: Config, a: ActorAddr, msg: Msg, c': Config) 
        requires push(c, a, msg, c')
        ensures WF_queue(c', a)
    {
    }
    
//TODO: Complete pop
    predicate pop(c:Config, a:ActorAddr, msg: Msg, c': Config){true} 
        


    /*


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
  */  
} 
