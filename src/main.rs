use actix_web::{get, post, web::{self, Json}, App, HttpRequest, HttpResponse, HttpServer, Responder,middleware};
use serde::{Deserialize, Serialize};
use std::{env, fs, io};
use std::sync::RwLock;
use rand::rngs::ThreadRng;

mod cfg;
/// create a tweet `/tweets`


#[actix_web::main]

async fn main() -> io::Result<()> {
    env::set_var("RUST_LOG", "actix_web=debug,actix_server=info");

    HttpServer::new(|| {
        App::new()
        .wrap(middleware::Logger::default())
            .service(cfg::set_gramm)
            .service(cfg::get_true_words)
            .service(cfg::get_words)
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
