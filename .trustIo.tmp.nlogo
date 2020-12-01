globals[
  time
  total_global_transactions ;  the global number of transactions
  number_of_nodes;
  current_ticks;
  number_of_malicous_nodes
  number_of_good_nodes
  security_treshold ; to vote trust score should be > security_treshold
  successful_transactions;
]
;globals variables hold values that are accessible anywhere in th program
;link parameters
links-own [
  weight ; each directed * is weighted
]
;;peer's parameters
turtles-own [
  security_score
  User_behavior
  service               ;;each node offer a certian number of services, we will use just 0 or 1
  total_transactions    ;;N of tx performed by the peer
  peer_trust_value        ;;peers label
  malicious             ;;is the peer malicious or not?
  list_time_of_feedback_given; a list of time_of_transaction. the time of the feedback given during a transaction
  list_time_of_transaction ; list of time_of_transaction which is the current tick

  list_satisfaction ; feedback for peer's actions => filled using get-satisfaction method for a given transaction
  list_credibility ;  list of normalised credebility values (for all peers); a random value generated by get-credebility fct [0-1]
  list_transaction_context_factor_value
  list_other_peer_id
]


to setup
  settings-initialization
  clear-all                       ;; clear everything on canvas
  setup-nodes                     ;; a procedure to set nodes
  ;setup-edges                     ;; a procedure to set edges
  setup-malicious-nodes
  ;ask turtles [ set color red]   ;; paint nodes red
  ask links [set color white]     ;; paint edges white
  reset-ticks
  layout
end
;--------------------------------------
;Network intialization
;-------------------------------------
to setup-nodes
  set-default-shape turtles "circle"
  set number_of_nodes number_of_peers ;number_peers is defined in the interface
  create-turtles number_of_nodes
  ask turtles
  [
    set color green
    set size 1.2

    ;;set service
    set service random 2;no_services_available ;either it provides the service or not !!2not1

    ;;initialise the initial trust values
    set peer_trust_value global_initial_trust_value

    ;;set the label for the nodes
    set label precision peer_trust_value 2 ;1.25 2 digits after .


    ;;set malicious status
    set malicious false

    ; for visual reasons, we don't put any nodes *too* close to the edges
    setxy (random-xcor * 0.95) (random-ycor * 0.95)
    
    initialize-turtle-lists self; initialize turtles lists and vars
  ]

end

to setup-malicious-nodes
    ;;set malicious peers according to percentage
  let n_malicious round ((number_of_nodes * number_of_malicious_nodes) / 100) ; malicious_peers % defined in the interface

  let malicious_peers_set n-of n_malicious turtles
  ask malicious_peers_set
  [
    set color red
    set malicious true
  ]


  ;;calculate number of malicous nodes in the network
  set number_of_malicous_nodes n_malicious
  ;;calculate number of good nodes
  set number_of_good_nodes number_of_nodes - number_of_malicous_nodes  
  show word "number of malicious peers :" number_of_malicous_nodes
end



to setup-edges
  let num-links  6

  while [ count links < num-links ] ;; num-links given by the user from interface
  [
    ask one-of turtles
    [
      let other_turtle one-of other turtles

      if other_turtle != nobody [ create-link-to other_turtle ]
      ask link-with other_turtle [
        set weight 10
        set label weight
       
      ]
      show word " new link:" link-with other_turtle
      ask link-with other_turtle[
          if weight = 0 ; for unkonw reason weight for some links isn't set in the previous operation
          [
          show word "error weigh detected and corrected" other_turtle
          set weight 10
          
        ]
          show word "wieight is" weight
      ]
    ]
  ]
    ; make the network look a little prettier
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end


;--------------------------------------
; Initialition and entrypoint
;-------------------------------------
to settings-initialization
  set security_treshold 0.2
end

to initialize-turtle-lists [peer]
  ;;initialise feedback lists
  set list_satisfaction []

end


to go
  if not any? turtles [stop] ;exits if there are no more turtles

  set current_ticks ticks
  
  transact
  
  ;layout
  tick
end

;--------------------------------------
; Functions
;-------------------------------------
to transact
  
   let peer1 one-of turtles
   evaluate-current-connections peer1
   let potential_partners_list find-potential_peers-to-connect-with 1 ;nodes providing the service
   show word "potential_partners_list " potential_partners_list 
    ;;check if there are items in the list
    let peer2 0

    ifelse length potential_partners_list < 1
    [
      stop ;;exit the procedure
    ]
    [
      ;;select a random peer
      let list_counter 0
    ifelse choose_random_or_most_trusted ; defined in the interface => choose most ranked node or at random
    [
      set peer2 item random (length potential_partners_list) potential_partners_list
    ]
    [
      set peer2 item 0 potential_partners_list ;;set the chosen peer to the most trusted peer
    ]
      while [([who] of peer2 = [who] of peer1) AND list_counter < length potential_partners_list]
      ;who holds the turtle's "who number" or ID number, an integer greater than or equal to zero.
      [
        set peer2 item list_counter potential_partners_list
        set list_counter list_counter + 1
      ]

      ;;final check
      if [who] of peer1 = [who] of peer2
      [
        stop ;;exit the procedure
      ]
    ]

    ;;perform the transaction between two peers
    perform-transaction peer1 peer2
end

;not mine
;;evaluates all the connections of a peer
;;the link is removed if the nodes trust value is below the threshold
to evaluate-current-connections [peer]
  ask peer
  [
    ask my-links ;the agentset containing all links
    [
      if [peer_trust_value] of other-end < trust_threshold
      [
        die ; ceases to exist
      ]
    ]
  ]
end

;Not mine
;;finding peers who offer the desired service
;;returns a list of the top [no_peers_to_return] peers
to-report find-potential_peers-to-connect-with [required-service] ; required-service is a parameter, the number of possible services is defined in the interface ==> here the random walk should be performed
  let potential_peers other turtles with [service = required-service]
  show word "potential_peers" potential_peers
  ;;determine the trust for each peer in the list
  ;ask potential_peers  <===========Compute the trust normaly
  ;[
    ;;set my_trust_value calculate-general-peer-trust self
    ;set peer_trust_value calculate-adaptive-trust self
    
    ;set label precision peer_trust_value 2
  ;]
  let no_peers_to_return 8 ; to change => N of peers to retun in the list 
  let sorted_list 0
  ;;return number of peers
  ifelse count potential_peers >= no_peers_to_return ;;list is small than number that needs to be returned
  [
    ;;sort the list and return only the first [no_peers_to_return]
    set sorted_list sublist ( sort-on [( - peer_trust_value)] potential_peers ) 0 no_peers_to_return
  ]
  [
    ;;sort the entire list
    set sorted_list sort-on [(- peer_trust_value)] potential_peers
  ]

  report sorted_list
end

;;this method performs the transaction part of a collaboration
to perform-transaction [peer1 peer2]

  ;;get the id of origional node
  let peer1_id [who] of peer1
  ;;get the id of other node
  let peer2_id [who] of peer2

  ;;get the exact time of the transaction
  let time_of_transaction current_ticks

  ;;get the context factor of the transaction
   

  ;;determing if any of the peers will act maliciously during this transaction
  let peer1_act_maliciously true
  let peer2_act_maliciously true

 
    ;;check peer1
    ;; peers would act maliously with a given probability defined in the interface
    ifelse [malicious] of peer1 ;;this peer is malicious ;; IMO malicious peers can act or not maliciously
    [
      if random 101 <= malicious_transactions_percentage ; % defined by interface and < 100
      [    set peer1_act_maliciously true      ]
    ]
    [      set peer1_act_maliciously false    ]

    ;;check peer2
    ifelse [malicious] of peer2 ;;this peer is malicious
    [ 
    if random 101 <= malicious_transactions_percentage    [        set peer2_act_maliciously true     ]
    ]
    [      set peer2_act_maliciously false    ]
 

  ;;perform actions via peer1
  ask turtle peer1_id
  [
    ;;update origional peer (peer1) feedback history based on the feedback from peer2
 
    ifelse peer2_act_maliciously
    [setup-feedback_edges_between peer1 peer2 -1]
    [setup-feedback_edges_between peer1 peer2 1]
    
    set total_transactions total_transactions + 1

   
 
   ]

  

  ;;determine if the transaction was successful
  if not peer1_act_maliciously AND not peer2_act_maliciously
  [
    set successful_transactions successful_transactions + 1
  ]

  ;;update the global number of transactions
  set total_global_transactions total_global_transactions + 1
end



to setup-feedback_edges_between [peer1 peer2 feedback] ; P1 => P2 
  
 
  show word "setting up edge between" peer1
  show word "and" peer2
    ask peer1
    [
      let other_turtle peer2

      if other_turtle != nobody [ create-link-to other_turtle ]
      ask link-with other_turtle [
        
        set weight weight + feedback
        set label weight
       
      ]
      show word " new link:" link-with other_turtle
      ask link-with other_turtle[
          if weight = 0 ; for unkonw reason weight for some links isn't set in the previous operation
          [
          show word "error weigh detected and corrected" other_turtle
          set weight weight + feedback
          
        ]
          show word "wieight is" weight
      ]
    ]
  
    ; make the network look a little prettier
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end
;-------------------------------
;Display settings
;--------------------------------

to layout
  ;; the number 3 here is arbitrary; more repetitions slows down the
  ;; model, but too few gives poor layouts
  repeat 3 [
    ;; the more turtles we have to fit into the same amount of space,
    ;; the smaller the inputs to layout-spring we'll need to use
    let factor sqrt count turtles
    ;; numbers here are arbitrarily chosen for pleasing appearance
    layout-spring turtles links (1 / factor) (7 / factor) (10 / factor)
    display  ;; for smooth animation
  ]
  ;; don't bump the edges of the world
  let x-offset max [xcor] of turtles + min [xcor] of turtles
  let y-offset max [ycor] of turtles + min [ycor] of turtles
  ;; big jumps look funny, so only adjust a little each time
  set x-offset limit-magnitude x-offset 0.1
  set y-offset limit-magnitude y-offset 0.1
  ask turtles [ setxy (xcor - x-offset / 2) (ycor - y-offset / 2) ]
end
to-report limit-magnitude [number limit]
  if number > limit [ report limit ]
  if number < (- limit) [ report (- limit) ]
  report number
end
