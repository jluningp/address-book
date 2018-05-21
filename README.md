# Address Book Binah Case Study

This is a case study for Binah (https://github.com/jbrown215/binah). It demonstrates what policies we can 
encode and check. 

## Policies 

```
Person
   email String {\viewer person -> userEmail viewer == personEmail person}
   UniquePerson email
   name {n : String | len n > 0} {\viewer person -> isVerified viewer}
   street {n : String | len n > 0} {\viewer person -> personFriendsWithUser person viewer}
   number {v:Int | v > 0} {\viewer person -> personFriendsWithUser person viewer}
   deriving Show
Friends
   email String {\viewer friend -> userEmail viewer == friendsEmail friend}
   UniqueFriend email
   requests [String] {\viewer friend -> userEmail viewer == friendsEmail friend}
   friends [String] {\viewer friend -> friendFriendsWithUser friend viewer}
   outgoingRequests [String] {\viewer friend -> userEmail viewer == friendsEmail friend}
```

Some of the measures (isVerified, personFriendsWithUser) are defined in [BinahLibrary](https://github.com/jluningp/address-book/blob/master/src/BinahLibrary.hs#L456-L480). 
`friendFriendsWithUser` would be identical to personFriendsWithUser except it would work on a `Friends`, rather than a `Person`.
These policies are also defined in [refined-models](https://github.com/jluningp/address-book/blob/master/config/refined-models).

## Tricky Problems

We have a couple of interesting problems that we still need to solve. 

### Carrying Around Context 

First, an annoyance: In Browse.hs, I would like to be able to compute a string for each person listed
(either "Click to send friend request.", "Friend request sent." or "Friends.") depending on the viewer's relationship 
with the person. Currently, the logic for this is spread over a couple of functions, but this would be a cleaner way 
to do it. This would be a TaggedPerson String.

```
...
taggedStatus <- getFriendshipStatusMessage person
```

When calling [`safeUnwrapPerson`](https://github.com/jluningp/address-book/blob/master/src/BinahLibrary.hs#L440-L446) on 
taggedStatus later on, I need to still know what person it was computed from

```
...
let status = safeUnwrapPerson person viewer taggedStatus 
in ...
```

### Two Taggeds? 

What happens if I compute a value from two different TaggedPersons?

```
sameName :: Tagged Person -> Tagged Person -> Tagged Bool
sameName person1 person2 = do 
   Person _ name1 _ _ <- person1
   Person _ name2 _ _ <- person2
   return $ name1 == name2
...
let areSame = sameName person1 person2 
in safeUnwrapPerson ??? viewer areSame
...
```

I can't call `safeUnwrapPerson` on `areSame`, since safeUnwrapPerson only takes one Person as input, but two
are needed (person1 and person2). 

